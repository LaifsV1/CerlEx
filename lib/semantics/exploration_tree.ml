type terminal_kind =
  | Real
  | Speculative
  | Cutoff

type node = {
    parent      : int option;
    depth       : int;
    speculative : bool;
    mutable expanded              : bool;
    mutable steps                 : int64;
      (** Reduction steps ([Reductions.big_step_one] calls) spent expanding
          THIS node into its children.  The configuration metric is this
          metric with every node weighted 1, so the two differ exactly where
          expansion effort is uneven -- a long deterministic computation
          costs one configuration but many steps. *)
    mutable overhead_steps        : int64;
      (** Reduction steps performed by exploration bookkeeping rather than by
          replaying a root-to-real-leaf execution.  These count toward online
          effort, but not toward the stateless replay counterfactual. *)
    mutable real_terminals        : int64;
    mutable speculative_terminals : int64;
    mutable cutoff_terminals      : int64;
  }

type t = {
    mutable nodes : node option array;
    mutable size  : int;
  }

type stats = {
    total_configurations                   : int64;
    expanded_configurations                : int64;
    real_prefix_configurations             : int64;
    speculative_suffix_configurations      : int64;
    speculative_subtree_configurations     : int64;
    stateless_replay_configurations        : int64;
    online_steps                           : int64;
    stateless_replay_steps                 : int64;
    repeated_prefix_configurations         : int64;
    net_saved_configurations               : int64;
    real_leaves                            : int64;
    speculative_leaves                     : int64;
    cutoff_leaves                          : int64;
    unresolved_configurations              : int64;
    mean_real_path_configurations          : float;
    max_real_path_configurations           : int;
  }

let fresh_node ~parent ~depth ~speculative =
  { parent
  ; depth
  ; speculative
  ; expanded = false
  ; steps = 0L
  ; overhead_steps = 0L
  ; real_terminals = 0L
  ; speculative_terminals = 0L
  ; cutoff_terminals = 0L
  }

let ensure_capacity tree id =
  if id < 0 then invalid_arg "Exploration_tree: negative node id";
  if id >= Array.length tree.nodes then begin
    let rec next_capacity n =
      if id < n then n else next_capacity (2 * n)
    in
    let capacity = next_capacity (max 1 (Array.length tree.nodes)) in
    let nodes = Array.make capacity None in
    Array.blit tree.nodes 0 nodes 0 (Array.length tree.nodes);
    tree.nodes <- nodes
  end

let find tree id =
  if id < 0 || id >= Array.length tree.nodes then
    invalid_arg "Exploration_tree: unknown node id"
  else
    match tree.nodes.(id) with
    | Some node -> node
    | None -> invalid_arg "Exploration_tree: unknown node id"

let create ~root_id ~root_speculative =
  let tree = { nodes = Array.make 16 None; size = 0 } in
  ensure_capacity tree root_id;
  tree.nodes.(root_id) <-
    Some (fresh_node ~parent:None ~depth:0 ~speculative:root_speculative);
  tree.size <- 1;
  tree

let add tree ~id ~parent ~speculative =
  ensure_capacity tree id;
  if Option.is_some tree.nodes.(id) then
    invalid_arg "Exploration_tree: duplicate node id";
  let parent_node = find tree parent in
  if parent >= id then
    invalid_arg "Exploration_tree: parent must precede child";
  tree.nodes.(id) <-
    Some (fresh_node ~parent:(Some parent)
            ~depth:(parent_node.depth + 1) ~speculative);
  tree.size <- tree.size + 1

let mark_expanded tree id =
  (find tree id).expanded <- true

(** Charge [n] reduction steps to [id]: the effort of expanding it. *)
let add_steps tree id n =
  if n < 0 then invalid_arg "Exploration_tree: negative step count";
  let node = find tree id in
  node.steps <- Int64.add node.steps (Int64.of_int n)

(** Charge [n] online-only reduction steps to [id]. *)
let add_overhead_steps tree id n =
  if n < 0 then invalid_arg "Exploration_tree: negative overhead step count";
  let node = find tree id in
  node.overhead_steps <- Int64.add node.overhead_steps (Int64.of_int n)

let mark_terminal ?(multiplicity = 1) tree id kind =
  if multiplicity <= 0 then
    invalid_arg "Exploration_tree: terminal multiplicity must be positive";
  let node = find tree id in
  let n = Int64.of_int multiplicity in
  match kind with
  | Real -> node.real_terminals <- Int64.add node.real_terminals n
  | Speculative ->
      node.speculative_terminals <- Int64.add node.speculative_terminals n
  | Cutoff -> node.cutoff_terminals <- Int64.add node.cutoff_terminals n

let stats tree =
  let capacity = Array.length tree.nodes in
  let real_descendants = Array.make capacity 0L in
  let speculative_descendants = Array.make capacity 0L in
  let cutoff_descendants = Array.make capacity 0L in
  let reaches_contiguous_speculative_suffix = Array.make capacity false in
  let total_configurations = ref 0L in
  let expanded_configurations = ref 0L in
  let real_prefix_configurations = ref 0L in
  let speculative_suffix_configurations = ref 0L in
  let speculative_subtree_configurations = ref 0L in
  let stateless_replay_configurations = ref 0L in
  let online_steps = ref 0L in
  let stateless_replay_steps = ref 0L in
  let real_leaves = ref 0L in
  let speculative_leaves = ref 0L in
  let cutoff_leaves = ref 0L in
  let unresolved_configurations = ref 0L in
  let max_real_path_configurations = ref 0 in
  for id = capacity - 1 downto 0 do
    match tree.nodes.(id) with
    | None -> ()
    | Some node ->
      total_configurations := Int64.succ !total_configurations;
      if node.expanded then
        expanded_configurations := Int64.succ !expanded_configurations;
      real_leaves := Int64.add !real_leaves node.real_terminals;
      speculative_leaves :=
        Int64.add !speculative_leaves node.speculative_terminals;
      cutoff_leaves := Int64.add !cutoff_leaves node.cutoff_terminals;
      if node.real_terminals > 0L then
        max_real_path_configurations :=
          max !max_real_path_configurations (node.depth + 1);
      let real = Int64.add real_descendants.(id) node.real_terminals in
      let speculative =
        Int64.add speculative_descendants.(id) node.speculative_terminals in
      let cutoff = Int64.add cutoff_descendants.(id) node.cutoff_terminals in
      real_descendants.(id) <- real;
      speculative_descendants.(id) <- speculative;
      cutoff_descendants.(id) <- cutoff;
      stateless_replay_configurations :=
        Int64.add !stateless_replay_configurations real;
      (* Same accumulation, weighted by expansion effort: a stateless replay
         redoes this node's steps once per real leaf beneath it. *)
      online_steps :=
        Int64.add !online_steps
          (Int64.add node.steps node.overhead_steps);
      stateless_replay_steps :=
        Int64.add !stateless_replay_steps (Int64.mul real node.steps);
      let in_contiguous_speculative_suffix =
        node.speculative
        && real = 0L
        && cutoff = 0L
        && (node.speculative_terminals > 0L
            || reaches_contiguous_speculative_suffix.(id)) in
      if real > 0L then
        real_prefix_configurations :=
          Int64.succ !real_prefix_configurations
      else if speculative > 0L && cutoff = 0L then begin
        speculative_subtree_configurations :=
          Int64.succ !speculative_subtree_configurations;
        if in_contiguous_speculative_suffix then
          speculative_suffix_configurations :=
            Int64.succ !speculative_suffix_configurations
      end else if speculative = 0L && cutoff = 0L then
        unresolved_configurations :=
          Int64.succ !unresolved_configurations;
      begin match node.parent with
      | None -> ()
      | Some parent ->
        if in_contiguous_speculative_suffix then
          reaches_contiguous_speculative_suffix.(parent) <- true;
        real_descendants.(parent) <-
          Int64.add real_descendants.(parent) real;
        speculative_descendants.(parent) <-
          Int64.add speculative_descendants.(parent) speculative;
        cutoff_descendants.(parent) <-
          Int64.add cutoff_descendants.(parent) cutoff
      end
  done;
  if Int64.of_int tree.size <> !total_configurations then
    failwith "Exploration_tree: inconsistent node count";
  let repeated_prefix_configurations =
    Int64.sub !stateless_replay_configurations
      !real_prefix_configurations in
  let net_saved_configurations =
    Int64.sub !stateless_replay_configurations
      !total_configurations in
  let mean_real_path_configurations =
    if !real_leaves = 0L then 0.0
    else
      Int64.to_float !stateless_replay_configurations
      /. Int64.to_float !real_leaves in
  { total_configurations = !total_configurations
  ; expanded_configurations = !expanded_configurations
  ; real_prefix_configurations = !real_prefix_configurations
  ; speculative_suffix_configurations =
      !speculative_suffix_configurations
  ; speculative_subtree_configurations =
      !speculative_subtree_configurations
  ; stateless_replay_configurations =
      !stateless_replay_configurations
  ; online_steps = !online_steps
  ; stateless_replay_steps = !stateless_replay_steps
  ; repeated_prefix_configurations
  ; net_saved_configurations
  ; real_leaves = !real_leaves
  ; speculative_leaves = !speculative_leaves
  ; cutoff_leaves = !cutoff_leaves
  ; unresolved_configurations = !unresolved_configurations
  ; mean_real_path_configurations
  ; max_real_path_configurations = !max_real_path_configurations
  }

let summary_line ~complete tree =
  let s = stats tree in
  let comparable =
    complete
    && s.cutoff_leaves = 0L
    && s.unresolved_configurations = 0L in
  if comparable then begin
    let classified =
      Int64.add s.real_prefix_configurations
        s.speculative_subtree_configurations in
    if classified <> s.total_configurations then
      failwith "Exploration_tree: complete tree does not partition into real prefixes and speculative subtrees";
    let derived_net_saved =
      Int64.sub s.repeated_prefix_configurations
        s.speculative_subtree_configurations in
    if derived_net_saved <> s.net_saved_configurations then
      failwith "Exploration_tree: inconsistent prefix-reuse accounting"
  end;
  let ratio =
    if s.total_configurations = 0L then 0.0
    else
      Int64.to_float s.stateless_replay_configurations
      /. Int64.to_float s.total_configurations in
  let step_ratio =
    if s.online_steps = 0L then 0.0
    else
      Int64.to_float s.stateless_replay_steps
      /. Int64.to_float s.online_steps in
  Printf.sprintf
    "[prefix] configurations: %Ld online, %Ld real-prefix, %Ld failed-speculative, %Ld speculative-subtree, %Ld same-tree stateless, %Ld repeated-prefix, %Ld net saved (%.2fx); leaves: %Ld real, %Ld speculative, %Ld cutoff; real path: %.2f mean, %d max; steps: %Ld online, %Ld stateless (%.2fx) (%s)"
    s.total_configurations
    s.real_prefix_configurations
    s.speculative_suffix_configurations
    s.speculative_subtree_configurations
    s.stateless_replay_configurations
    s.repeated_prefix_configurations
    s.net_saved_configurations
    ratio
    s.real_leaves
    s.speculative_leaves
    s.cutoff_leaves
    s.mean_real_path_configurations
    s.max_real_path_configurations
    s.online_steps
    s.stateless_replay_steps
    step_ratio
    (if comparable then "complete" else "not comparable")

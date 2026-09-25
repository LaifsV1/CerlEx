(* monadic definitions *)

module Option_ext = struct
  type 'a t = 'a option

  let return x = Some x
  let some x = Some x
  let none = None

  let bind o f =
    match o with
    | Some x -> f x
    | None -> None

  let map f o =
    match o with
    | Some x -> Some (f x)
    | None -> None

  let iter f = function
    | Some x -> f x
    | None -> ()

  let fold ~none ~some = function
    | Some x -> some x
    | None -> none

  let join = function
    | Some x -> x
    | None -> None

  let both a b =
    match a, b with
    | Some x, Some y -> Some (x, y)
    | _ -> None

  let all xs =
    let rec go acc = function
      | [] -> Some (List.rev acc)
      | Some x :: tl -> go (x :: acc) tl
      | None :: _ -> None
    in
    go [] xs

  let first_some a b =
    match a with
    | Some _ -> a
    | None -> b

  let is_some = function
    | Some _ -> true
    | None -> false

  let is_none o = not (is_some o)

  module Infix = struct
    let ( >>= ) o f = bind o f
    let ( =<< ) f o = bind o f
    let ( >|= ) o f = map f o
    let ( <*> ) fo xo =
      match fo, xo with
      | Some f, Some x -> Some (f x)
      | _ -> None
  end

  module Syntax = struct
    let ( let* ) = bind
    let ( let+ ) x f = map f x
    let ( and* ) = both
    let ( and+ ) = both
  end
end

module Result_ext = struct
  type ('a, 'e) t = ('a, 'e) Stdlib.result

  let return x = Ok x
  let ok x = Ok x
  let error e = Error e

  let bind r f =
    match r with
    | Ok x -> f x
    | Error e -> Error e

  let map f r =
    match r with
    | Ok x -> Ok (f x)
    | Error e -> Error e

  let map_error f r =
    match r with
    | Ok x -> Ok x
    | Error e -> Error (f e)

  let iter f = function
    | Ok x -> f x
    | Error _ -> ()

  let fold ~ok ~error = function
    | Ok x -> ok x
    | Error e -> error e

  let join = function
    | Ok x -> x
    | Error e -> Error e

  let both a b =
    match a, b with
    | Ok x, Ok y -> Ok (x, y)
    | Error e, _ -> Error e
    | _, Error e -> Error e

  let all xs =
    let rec go acc = function
      | [] -> Ok (List.rev acc)
      | Ok x :: tl -> go (x :: acc) tl
      | Error e :: _ -> Error e
    in
    go [] xs

  let is_ok = function
    | Ok _ -> true
    | Error _ -> false

  let is_error r = not (is_ok r)

  module Infix = struct
    let ( >>= ) r f = bind r f
    let ( =<< ) f r = bind r f
    let ( >|= ) r f = map f r
    let ( >!| ) r f = map_error f r
    let ( <*> ) rf rx =
      match rf, rx with
      | Ok f, Ok x -> Ok (f x)
      | Error e, _ -> Error e
      | _, Error e -> Error e
  end

  module Syntax = struct
    let ( let* ) = bind
    let ( let+ ) x f = map f x
    let ( and* ) = both
    let ( and+ ) = both
  end
end

module Option_syntax = Option_ext.Syntax
module Result_syntax = Result_ext.Syntax
module Option_infix = Option_ext.Infix
module Result_infix = Result_ext.Infix

(* list definitions *)

let take n l =
  let[@tail_mod_cons] rec aux n l =
    match n, l with
    | 0, _ | _, [] -> []
    | n, x::l -> x::aux (n - 1) l
  in
  if n < 0 then invalid_arg "List.take";
  aux n l

let drop n l =
  let rec aux i = function
    | _x::l when i < n -> aux (i + 1) l
    | rest -> rest
  in
  if n < 0 then invalid_arg "List.drop";
  aux 0 l

let take_while p l =
  let[@tail_mod_cons] rec aux = function
    | x::l when p x -> x::aux l
    | _rest -> []
  in
  aux l

let rec drop_while p = function
  | x::l when p x -> drop_while p l
  | rest -> rest

let map_uniq f xs =
  xs |> List.map f |> List.sort_uniq compare

let rec cartesian_product = function
  | [] -> [[]]
  | xs :: xss ->
     let rest = cartesian_product xss in
     List.concat_map (fun x ->
         List.map (fun ys -> x :: ys) rest
       ) xs

let cartesian_product_tr l =
  let rec aux acc = function
    | [] ->  acc
    | xs :: xss ->
       let acc' =
         List.concat_map (fun x ->
             List.map (fun ys -> x :: ys) acc
           ) xs
       in
       aux acc' xss
  in
  aux [[]] l

(** fastest cartesian product from rosetta code -- base case was modified because it was wrong *)
let rec cartesian_product_fast l = 
    (* We need to do the cross product of our current list and all the others
     * so we define a helper function for that *)
    let rec aux ~acc l1 l2 = match l1, l2 with
    | [], _ | _, [] -> acc
    | h1::t1, h2::t2 -> 
        let acc = (h1::h2)::acc in
        let acc = (aux ~acc t1 l2) in
        aux ~acc [h1] t2
    (* now we can do the actual computation *)
    in match l with
    | [] -> [[]]
    | [l1] -> List.map (fun x -> [x]) l1
    | l1::tl ->
        let tail_product = cartesian_product_fast tl in
        aux ~acc:[] l1 tail_product

let cartesian_power (choices : 'a list) (n : int) :('a list list) =
  let rec cartesian_power_aux (paths : 'a list list) (n : int) (choices) :('a list list) =
    (* function to add all choices to a path *)
    let add_choices_to_one_path path acc =
      List.fold_left (fun acc c -> (c :: path) :: acc) acc choices
    in
    (* if n = 0 just output the paths *)
    if n = 0 then paths else
      (* for every path, add all choices *)
      cartesian_power_aux (List.fold_left (fun acc p -> add_choices_to_one_path p acc) [] paths) (n-1) choices
  in
  cartesian_power_aux [[]] n choices


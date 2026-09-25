-module(control).
-export([init/4]).

% create N processes 1 .. N and return a dict from
% 1..N to Pids
create(_, 0, Dict) -> Dict ;
create(Module, N, Dict) ->
  % spawn create a new process executing the proc function with argument nil
  Id = spawn(Module, proc, [nil]),
  Id ! init_state,
  create(Module, N-1, dict:append(N, Id, Dict)).

% broadcast a Signal to all processes in Dict
broadcast(Dict, Signal) ->
  F = fun (_, [Y]) -> Y ! Signal end,
  dict : map (F, Dict),
  ok.

% send a Signal to process Dict(I)
send(Dict, I, Signal) ->
  [Id] = dict : fetch(I, Dict),
  Id ! Signal,
  ok.

% wait for N ok signals
syncr(0) -> ok;
syncr(N) ->
  receive
    ok ->
        % io : format("ok received ~n", [])
        syncr(N-1)
  end.

% init neighbors according to topology Graph
init_topology(Dict, Graph) ->
  F = fun(X) -> [Res] = dict : fetch(X, Dict), Res end,
  IdToPId = fun(L) -> lists : map(F, L) end,
  G = fun (I, [Y]) ->
      [LId] = dict : fetch(I, Graph),
      LPId = IdToPId(LId),
      Y ! {neighbors, LPId, self()} end,
  dict : map (G, Dict),
  ok.

% init all states with unary function Signal : I -> term.
init_state(Dict, Signal) ->
  F = fun (I, [Y]) -> Y ! {init, Signal(I), self()} end,
  dict : map (F, Dict),
  ok.

% init all process according to the given topology and Signal : I -> term
% returns a pair of function Send and Broadcast
init(Module, N, Graph, Signal) ->
  Dict = create(Module, N, dict:new()),
  init_topology(Dict, Graph),
  init_state(Dict, Signal),
  syncr(2 * N),
  io : format("Initialization ok~n", []),
  Send = fun (I, S) -> send(Dict, I, S) end,
  Broadcast = fun (S) -> broadcast(Dict, S) end,
  { Send, Broadcast }.

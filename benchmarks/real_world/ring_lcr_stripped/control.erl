-module(control).
-export([init/4]).

create(_, 0, Dict) -> Dict;
create(Module, N, Dict) ->
    Id = spawn(Module, proc, [nil]),
    Id ! init_state,
    create(Module, N-1, dict:append(N, Id, Dict)).

broadcast(Dict, Signal) ->
    F = fun(_, [Y]) -> Y ! Signal end,
    dict:map(F, Dict),
    ok.

send(Dict, I, Signal) ->
    [Id] = dict:fetch(I, Dict),
    Id ! Signal,
    ok.

syncr(0) -> ok;
syncr(N) ->
    receive ok -> syncr(N-1) end.

init_topology(Dict, Graph) ->
    F = fun(X) -> [Res] = dict:fetch(X, Dict), Res end,
    IdToPId = fun(L) -> lists:map(F, L) end,
    G = fun(I, [Y]) ->
        [LId] = dict:fetch(I, Graph),
        LPId = IdToPId(LId),
        Y ! {neighbors, LPId, self()}
    end,
    dict:map(G, Dict),
    ok.

init_state(Dict, Signal) ->
    F = fun(I, [Y]) -> Y ! {init, Signal(I), self()} end,
    dict:map(F, Dict),
    ok.

init(Module, N, Graph, Signal) ->
    Dict = create(Module, N, dict:new()),
    init_topology(Dict, Graph),
    init_state(Dict, Signal),
    syncr(2 * N),
    Send = fun(I, S) -> send(Dict, I, S) end,
    Broadcast = fun(S) -> broadcast(Dict, S) end,
    {Send, Broadcast}.

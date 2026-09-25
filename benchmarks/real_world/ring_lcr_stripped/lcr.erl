-module(lcr).
-export([proc/1]).

-record(state, {uin = 0, neighbors = nil}).

broadcast(U, Neighbors) ->
    F = fun(X) -> X ! {msg, U} end,
    lists:map(F, Neighbors).

proc(State) ->
    receive
        init_state -> proc(#state{});
        {neighbors, N, Sender} ->
            Sender ! ok,
            proc(State#state{neighbors = N});
        {init, U, Sender} ->
            Sender ! ok,
            proc(State#state{uin = U});
        start ->
            broadcast(State#state.uin, State#state.neighbors),
            proc(State);
        {msg, U} ->
            if
                U > State#state.uin ->
                    broadcast(U, State#state.neighbors),
                    proc(State);
                U == State#state.uin ->
                    proc(State);
                U < State#state.uin -> proc(State)
            end;
        quit -> ok
    end.

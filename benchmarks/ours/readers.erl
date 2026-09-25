-module(readers).
-export([main/0]).

%% Message-passing equivalent of the readers benchmark from Abdulla et al. POPL'14.
%% The ETS table is replaced by a register process holding shared state.
%%
%% Structure: one writer sets the shared value to 42; N readers each read it.
%% Race: a reader sees 0 (old) or 42 (new) depending on whether it reads
%% before or after the writer.
%%
%% For N=2: optimal-DPOR finds 4 traces, classic DPOR finds 5 (Table 2).
%% Our exhaustive exploration finds more, since it also distinguishes the
%% order in which independent reads are scheduled.

reg(Val) ->
    receive
        {write, V}    -> reg(V);
        {read, From}  -> From ! Val, reg(Val)
    end.

main() ->
    Reg = spawn(fun() -> reg(0) end),
    spawn(fun() -> Reg ! {write, 42} end),
    spawn(fun() ->
        Reg ! {read, self()},
        receive V -> io:format("r1: ~w~n", [V]) end
    end),
    spawn(fun() ->
        Reg ! {read, self()},
        receive V -> io:format("r2: ~w~n", [V]) end
    end).

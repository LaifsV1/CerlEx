-module(readers_n).
-export([main/0]).

reg(Val) ->
    receive
        {write, V}   -> reg(V);
        {read, From} -> From ! Val, reg(Val)
    end.

spawn_readers(0, _, _) -> ok;
spawn_readers(N, Reg, Id) ->
    spawn(fun() ->
        Reg ! {read, self()},
        receive V -> io:format("r~w: ~w~n", [Id, V]) end
    end),
    spawn_readers(N - 1, Reg, Id + 1).

main() ->
    N = 3,
    Reg = spawn(fun() -> reg(0) end),
    spawn(fun() -> Reg ! {write, 42} end),
    spawn_readers(N, Reg, 1).

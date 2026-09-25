-module(parallel_relay_race).
-export([main/0]).

%% Two parallel relay paths to Receiver, both going through a receive step.
%% RelayA receives from Sender and forwards directly.
%% RelayB receives from Sender and spawns a process to do the final send.
%% Receiver outputs whichever message arrives first.

main() ->
    Self = self(),
    RelayA = spawn(fun() -> receive Msg -> Self ! Msg end end),
    RelayB = spawn(fun() ->
        receive Msg ->
            spawn(fun() -> Self ! Msg end)
        end
    end),
    spawn(fun() -> RelayA ! relay_a, RelayB ! relay_b end),
    receive X -> io:format("~w~n", [X]) end.

-module(spawn_race).
-export([main/0]).

%% Sender delivers two distinguishable messages to Receiver via two routes:
%%   direct:  Sender -> Receiver  (sends `direct`)
%%   indirect: Sender spawns a process -> Receiver  (sends `spawned`)
%% Receiver outputs whichever message arrives first.

main() ->
    Self = self(),
    spawn(fun() ->
        Self ! direct,
        spawn(fun() -> Self ! spawned end)
    end),
    receive X -> io:format("~w~n", [X]) end.

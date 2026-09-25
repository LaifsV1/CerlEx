-module(spawn_race2).
-export([main/0]).

%% Like spawn_race, but spawn comes before the direct send, so both
%% message orderings are causally reachable.  Both CerlEx and Concuerror
%% should find 2 traces.

main() ->
    Self = self(),
    spawn(fun() ->
        spawn(fun() -> Self ! spawned end),
        Self ! direct
    end),
    receive X -> io:format("~w~n", [X]) end.

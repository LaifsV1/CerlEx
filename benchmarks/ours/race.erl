-module(race).
-export([main/0]).

%% Two workers race to send their result to main.
%% Both sends land in main's inbox before main is scheduled to receive,
%% so main can receive from either — two branches, two possible outputs.
main() ->
    Self = self(),
    spawn(fun() -> Self ! {result, 1} end),
    spawn(fun() -> Self ! {result, 2} end),
    receive
        {result, X} -> io:format("~w~n", [X])
    end.

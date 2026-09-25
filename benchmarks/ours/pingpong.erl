-module(pingpong).
-export([main/0]).

main() ->
    Parent = self(),
    Child = spawn(fun() ->
        receive
            {ping, From} -> From ! pong
        end
    end),
    Child ! {ping, Parent},
    receive
        pong -> io:format("pong~n")
    end.

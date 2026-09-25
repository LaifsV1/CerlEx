-module(spawn3).
-export([main/0, worker/1]).

worker(Caller) -> Caller ! hello.

main() ->
    spawn(spawn3, worker, [self()]),
    receive Msg -> Msg end.

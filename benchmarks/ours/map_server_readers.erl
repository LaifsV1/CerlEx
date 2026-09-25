-module(map_server_readers).
-export([main/0]).

%% NOT an ETS test: the store is a process holding a `maps` value, queried by
%% message.  It was called `ets_readers` because it is the message-passing
%% analogue of Concuerror's ETS `readers` benchmark, but the name reads as an
%% ETS test and it was nearly excluded from the message-only exploration
%% profile on that basis.  Renamed 2026-09-21.

store_server(Store) ->
    receive
        {write, Key, Val} ->
            store_server(maps:put(Key, Val, Store));
        {read, From, Key} ->
            Val = maps:get(Key, Store, not_found),
            From ! {reply, Key, Val},
            store_server(Store)
    end.

readers(N) ->
    Tab = spawn(fun() -> store_server(maps:new()) end),
    Writer = fun() -> Tab ! {write, x, 42} end,
    Reader = fun(I) ->
        Tab ! {read, self(), I},
        receive {reply, I, _} -> ok end,
        Tab ! {read, self(), x},
        receive {reply, x, _} -> ok end
    end,
    spawn(Writer),
    [spawn(fun() -> Reader(I) end) || I <- lists:seq(1, N)],
    receive after infinity -> deadlock end.

main() ->
    readers(2).

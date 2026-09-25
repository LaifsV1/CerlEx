-module(skipped_match_wait_spurious).
-export([test/0, first/1, second/1]).

test() ->
    Self = self(),
    spawn(?MODULE, first, [Self]),
    receive
        work ->
            spawn(?MODULE, second, [Self]),
            receive
                {From, res} ->
                    case From of
                        first -> ok;
                        second -> erlang:error(spurious_future_res)
                    end
            end
    end.

first(Parent) ->
    Parent ! {first, res},
    Parent ! work.

second(Parent) ->
    Parent ! {second, res}.

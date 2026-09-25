-module(same_sender_skip_probe).
-export([test/0, sender/1]).

test() ->
    Self = self(),
    spawn(?MODULE, sender, [Self]),
    receive
        work ->
            receive
                res -> ok
            after 0 ->
                missing_res
            end
    end.

sender(Parent) ->
    Parent ! res,
    Parent ! work.

% Same-sender FIFO visibility witness.
%
% Expected (Erlang): no error.  The sender sends `res` before `work` to the
% same receiver. If the receiver can receive the later `work`, then the earlier
% `res` from the same sender must already be visible in the mailbox too.
% Selective receive may skip `res` to match `work`, but the following receive
% for `res` should succeed.
%
% Historical bug: CerlEx used to produce 2 traces, one with
% error:missing_res.  The channel model could select/deliver the later
% same-sender `work` while the earlier `res` remained unavailable, then time out
% waiting for `res`.
%
% This is FIFO evidence, not instant-delivery evidence. It says that once the
% later same-sender message is received, the earlier same-sender message must be
% visible too. It does not say both messages had to be delivered immediately
% when sent.
-module(same_sender_fifo_receive).
-export([main/0, sender/1]).

main() ->
    Self = self(),
    spawn(?MODULE, sender, [Self]),
    receive
        work ->
            receive
                res -> ok
            after 0 ->
                erlang:error(missing_res)
            end
    end.

sender(Parent) ->
    Parent ! res,
    Parent ! work.

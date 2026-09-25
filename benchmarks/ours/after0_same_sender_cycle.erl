%% Minimal same-sender after 0 example -- the witness that drove the wait-branch
%% timeout-disabling fix in scheduler.ml.
%%
%% The worker first asks for work.  After the server replies with `job`, the
%% worker sends `res` and then a later `{work, Worker}` request to the same
%% server.  The server then reaches `receive res after 0 -> receive {work,_}`.
%%
%% Before the fix CerlEx found 3 traces: one OK plus TWO errors.  The two error
%% traces differ only in whether the server timed out before or after the worker
%% sent -- but the timeout is mailbox-independent and commutes with that send, so
%% they reach the same state.  The redundant one came from a Waiting branch that
%% deferred the (already-explored) timeout and re-offered it next round.  The fix
%% disables the timeout on the Waiting branch (rewrites it to 'infinity'), so the
%% timeout fires in exactly one position.  CerlEx now matches Concuerror at 2.
%%
%% Current behaviour:
%%   CerlEx:     2 real traces, 1 uncaught exception
%%   Concuerror: 2 interleavings, 1 error (instant_delivery true and false)
-module(after0_same_sender_cycle).
-export([test/0, worker/1]).

test() ->
    Self = self(),
    spawn(?MODULE, worker, [Self]),
    receive
        {work, W} -> W ! job
    end,
    receive
        res -> ok
    after 0 ->
        receive
            {work, _W} -> erlang:error(spurious_work_after_res)
        end
    end.

worker(Server) ->
    Server ! {work, self()},
    receive
        job ->
            Server ! res,
            Server ! {work, self()}
    end.

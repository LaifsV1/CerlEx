-module(recv_fifo_cycle).
-export([recv_fifo_cycle/0, test/0]).

%% Pure message-passing joint-consistency witness (no ETS): refutes the
%% belief that receive is exempt from arrival-order cycle checking because
%% mailboxes are single-consumer and consumption is destructive.
%%
%% Measured 2026-07-13: Concuerror 2/2 interleavings, 0 errors; CerlEx
%% 3 real traces, 1 uncaught exception.  The spurious trace is
%% [X = one, Y = two] (the badmatch).  Writing arr() for mailbox arrival
%% order, that trace commits
%%   arr(A2) < arr(B2)   (first receive consumed A2; B2 matches too, so it
%%                        was absent or arrival-later -- either way this holds)
%%   arr(B1) < arr(A1)   (inner receive consumed B1 while A1, which arrived
%%                        before the already-consumed A2, matches)
%% and per-sender FIFO gives arr(A1) < arr(A2) and arr(B2) < arr(B1):
%%   A1 < A2 < B2 < B1 < A1  -- no arrival order exists.
%% A selective receive consumes one message destructively but passes over the
%% rest non-destructively; the FIFO backbone points upward from the skipped
%% survivor (A1) to the consumed later message (A2), so one consumer's
%% successive commits close a cross-sender cycle.  same_sender_visible cannot
%% see it (the flag is same-sender only).  See notes/observation_semantics.tex
%% section "Joint consistency" and notes/ets_order_graph_plan.md.

recv_fifo_cycle() ->
    P = self(),
    spawn(fun() -> P ! {1, one}, P ! {2, one} end),   % A1, A2
    spawn(fun() -> P ! {2, two}, P ! {1, two} end),   % B2, B1
    receive
        {2, X} ->
            case X of
                one ->
                    receive
                        {1, Y} -> one = Y
                    end;
                two ->
                    ok
            end
    end.

test() ->
    recv_fifo_cycle().

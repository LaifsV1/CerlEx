%% Demonstrates that the sleep-set wake clock gate is not vacuous.
%%
%% R has `msg` available from main and can either receive it or take `after 0`.
%% The branch where R waits is parkable because a ticker process sends main an
%% independent `tick`, giving main a receive sibling in the same schedule round;
%% without that kept sibling the all-waiting branch is dropped before the sleep
%% set sees it.
%%
%% In the timeout sibling, R sends `do` to A. A then sends `go` to B, and B sends
%% a later `msg` to R. That later message causally depends on R's timeout path:
%% its send clock has R's component greater than R's park component. The wake
%% gate `send_clock[R] =< park_comp` therefore rejects the wake. Removing the
%% gate spuriously wakes one extra parked configuration.
%%
%% Measured with the current scheduler:
%%   configurations: 14 pushed, 1 speculative
%% Measured with the wake gate removed:
%%   configurations: 15 pushed, 2 speculative
-module(sleep_set_clock_gate_probe).
-export([main/0]).

main() ->
  A = self(),
  R = spawn(fun() -> r(A) end),
  B = spawn(fun() -> b(R) end),
  spawn(fun() -> A ! tick end),
  R ! msg,
  receive
    tick -> ok;
    got_msg -> ok;
    do -> B ! go
  end,
  receive
    got_msg -> ok;
    do -> B ! go
  after 0 ->
    ok
  end.

r(A) ->
  receive
    msg -> A ! got_msg
  after 0 ->
    A ! do
  end.

b(R) ->
  receive
    go -> R ! msg
  end.

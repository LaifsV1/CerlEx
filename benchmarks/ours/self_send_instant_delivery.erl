%% Self-send instant-delivery witness.
%%
%% Concuerror immediately enqueues `self() ! tick` even with
%% `--instant_delivery false`, so a later child send cannot overtake it and only
%% `got_tick` is possible.
%%
%% CerlEx deliberately treats self-send like every other asynchronous send, so
%% the child message may be delivered first.  The two traces are required by
%% CerlEx's model; this test records the intentional model difference.
-module(self_send_instant_delivery).
-export([main/0]).

main() ->
  A = self(),
  A ! tick,
  spawn(fun() -> A ! other end),
  receive
    tick -> got_tick;
    other -> got_other
  end.

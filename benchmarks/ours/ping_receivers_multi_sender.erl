-module(ping_receivers_multi_sender).
-export([main/0, start/3]).

main() ->
  start(3, 1, 2).

start(NReceivers, MRounds, NSenders) ->
  Receivers = [
    spawn(fun() -> receiver_loop(NSenders) end)
    || _ <- lists:seq(1, NReceivers)
  ],

  Senders = [
    spawn(fun() -> sender_loop(Receivers, MRounds) end)
    || _ <- lists:seq(1, NSenders)
  ],

  {ok, Senders}.

receiver_loop(StopsLeft) ->
  receive
    {ping, Sender, Round} ->
      Sender ! {pong, self(), Round},
      receiver_loop(StopsLeft);

    stop ->
      case StopsLeft - 1 of
        0 ->
          ok;
        NewStopsLeft ->
          receiver_loop(NewStopsLeft)
      end
  end.

sender_loop(Receivers, 0) ->
  lists:foreach(
    fun(Receiver) ->
      Receiver ! stop
    end,
    Receivers
  ),
  ok;

sender_loop(Receivers, M) ->
  Round = M,

  lists:foreach(
    fun(Receiver) ->
      Receiver ! {ping, self(), Round}
    end,
    Receivers
  ),

  wait_for_replies(length(Receivers), Round),
  sender_loop(Receivers, M - 1).

wait_for_replies(0, _Round) ->
  ok;

wait_for_replies(N, Round) ->
  receive
    {pong, _Receiver, Round} ->
      wait_for_replies(N - 1, Round)
  end.

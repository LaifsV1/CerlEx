-module(ping_receivers).
-export([main/0, start/2]).

main() ->
  start(3, 3).

start(N, M) ->
  Receivers = [spawn(fun receiver_loop/0) || _ <- lists:seq(1, N)],
  Sender = spawn(fun() -> sender_loop(Receivers, M) end),
  {ok, Sender}.

receiver_loop() ->
  receive
    {ping, Sender, Round} ->
      Sender ! {pong, self(), Round},
      receiver_loop();

    stop ->
      ok
  end.

sender_loop(Receivers, 0) ->
  lists:foreach(
    fun(Receiver) ->
      Receiver ! stop
    end,
    Receivers
  ),
  io:format("Finished.~n"),
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

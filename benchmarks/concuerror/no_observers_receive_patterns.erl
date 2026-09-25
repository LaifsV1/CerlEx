-module(no_observers_receive_patterns).

-compile(export_all).

scenarios() ->
  [ test
  ].

test() ->
  P = self(),
  Fun = fun() -> P ! self() end,
  P1 = spawn(Fun),
  P2 = spawn(Fun),
  receive
    P1 ->
      receive
        P2 ->
          ok
      end
  end.

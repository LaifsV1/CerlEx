-module(alltoall7).
-export([main/0]).

%% Seven processes (main + six workers): each sends {msg, self()} to every
%% other, then receives one message.
%% Branching: 6^7 = 279,936 terminal traces.

send_all([], _) -> ok;
send_all([H|T], Msg) -> H ! Msg, send_all(T, Msg).

worker() ->
    receive
        {peers, Others} ->
            Self = self(),
            send_all(Others, {msg, Self}),
            receive
                {msg, _From} -> ok
            end
    end.

main() ->
    Self = self(),
    P1 = spawn(fun() -> worker() end),
    P2 = spawn(fun() -> worker() end),
    P3 = spawn(fun() -> worker() end),
    P4 = spawn(fun() -> worker() end),
    P5 = spawn(fun() -> worker() end),
    P6 = spawn(fun() -> worker() end),
    P1 ! {peers, [P2, P3, P4, P5, P6, Self]},
    P2 ! {peers, [P1, P3, P4, P5, P6, Self]},
    P3 ! {peers, [P1, P2, P4, P5, P6, Self]},
    P4 ! {peers, [P1, P2, P3, P5, P6, Self]},
    P5 ! {peers, [P1, P2, P3, P4, P6, Self]},
    P6 ! {peers, [P1, P2, P3, P4, P5, Self]},
    Others = [P1, P2, P3, P4, P5, P6],
    send_all(Others, {msg, Self}),
    receive
        {msg, From} -> io:format("~w~n", [From])
    end.

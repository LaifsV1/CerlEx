-module(alltoall).
-export([main/0]).

%% Four processes (main + three workers) each participating symmetrically:
%%   1. send {msg, self()} to every other process
%%   2. receive one {msg, From}
%%   3. send {relay, From} to every other process
%% Main additionally prints what it receives in each phase.
%%
%% Because all four processes send before any receive is scheduled,
%% each process has three incoming messages when the scheduler first
%% branches — yielding 3^4 = 81 combinations at the first schedule point,
%% then 3 more for main's relay receive: 243 terminal traces in total.

send_all([], _) -> ok;
send_all([H|T], Msg) -> H ! Msg, send_all(T, Msg).

worker() ->
    receive
        {peers, Others} ->
            Self = self(),
            send_all(Others, {msg, Self}),
            receive
                {msg, From} ->
                    send_all(Others, {relay, From})
            end
    end.

main() ->
    Self = self(),
    P1 = spawn(fun() -> worker() end),
    P2 = spawn(fun() -> worker() end),
    P3 = spawn(fun() -> worker() end),
    P1 ! {peers, [P2, P3, Self]},
    P2 ! {peers, [P1, P3, Self]},
    P3 ! {peers, [P1, P2, Self]},
    Others = [P1, P2, P3],
    send_all(Others, {msg, Self}),
    receive
        {msg, From} ->
            io:format("msg ~w~n", [From]),
            send_all(Others, {relay, From})
    end,
    receive
        {relay, X} ->
            io:format("relay ~w~n", [X])
    end.

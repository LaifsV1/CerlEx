-module(receive_obs_ov_min).
-export([receive_obs_ov_min/0, test/0]).

%% Minimal receive-only witness for the observable-others over-approximation.
%%
%% Sender S1 sends:
%%   A1 = {1, one}
%%   A2 = {2, one}
%%
%% Sender S2 sends:
%%   B2 = {2, two}
%%   B1 = {1, two}
%%
%% CerlEx currently accepts the receive vector:
%%   R2 receives A2 = {2, one}
%%   R1 receives B1 = {1, two}
%%
%% A single mailbox order would need:
%%   A1 < A2            (S1 send/delivery order)
%%   A2 < B2            (R2 got A2 before B2 could win; if B2 arrived later,
%%                       it still had to arrive before B1)
%%   B2 < B1            (S2 send/delivery order)
%%   B1 < A1            (R1 picked B1 while A1 was still pending)
%%
%% This cycle is impossible, so the badmatch branch is spurious.

receive_obs_ov_min() ->
    P = self(),
    spawn(fun() ->
        P ! {1, one},
        P ! {2, one}
    end),
    spawn(fun() ->
        P ! {2, two},
        P ! {1, two}
    end),
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
    receive_obs_ov_min().

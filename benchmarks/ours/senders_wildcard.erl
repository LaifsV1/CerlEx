-module(senders_wildcard).
-export([main/0]).

%% N processes each send a distinct message to R.
%% R does a single wildcard receive.
%% Only the first delivery matters; subsequent sends are independent of R.
%%
%% Traces: N (one per possible first message received).
%% Our tool: N branches at R's receive (N eligible channels) — optimal.
%%
%% Local CerlEx encoding of the "branch needed" observer example from
%% notes/optimal_dpor_observers_summary.md.  That note summarises the
%% non-selective receive scenario discussed in ODPOR with Observers
%% (Aronis et al., TACAS 2018), Section 2.  This module is not copied
%% from the paper or from the Concuerror test suite.

main() ->
    N = 4,
    R = self(),
    Msgs = lists:seq(1, N),
    [spawn(fun() -> R ! I end) || I <- Msgs],
    receive X ->
        io:format("first: ~w~n", [X])
    end.

-module(senders_ordered).
-export([main/0]).

%% N processes each send a distinct message M_i to R.
%% R receives them in a fixed order: first M_1, then M_2, ..., then M_N.
%% The sends are independent — no receive can observe their relative order.
%%
%% Traces: 1. Our tool is optimal: at each of R's receives, exactly one
%% channel has a matching message, so no branching occurs.
%%
%% Local CerlEx encoding of the "no branch" observer example from
%% notes/optimal_dpor_observers_summary.md.  That note summarises the
%% selective receive scenario discussed in ODPOR with Observers
%% (Aronis et al., TACAS 2018), Section 2.  This module is not copied
%% from the paper or from the Concuerror test suite.

main() ->
    R = self(),
    spawn(fun() -> R ! msg1 end),
    spawn(fun() -> R ! msg2 end),
    spawn(fun() -> R ! msg3 end),
    spawn(fun() -> R ! msg4 end),
    receive msg1 ->
        receive msg2 ->
            receive msg3 ->
                receive msg4 ->
                    io:format("ok~n")
                end
            end
        end
    end.

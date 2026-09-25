-module(tagged_selective).
-export([main/0]).

%% Tagged selective receive — the key observer example from TACAS 2018.
%%
%% p sends {b, self()} then {a, self()} to R.
%% q sends {a, self()} to R.
%% s sends {b, self()} to R.
%% R receives {a, X} first; if X is p then also receives {b, _}.
%%
%% R's first receive observes the race between p's {a,...} and q's {a,...}.
%% R's second receive (taken only if X=p) observes p's {b,...} vs s's {b,...}.
%% The current channel model does not track a global cross-sender mailbox order,
%% so both b-branches are kept.
%%
%% Traces with optimal DPOR with observers: 2.
%% Our tool: 3.
%%
%% Local CerlEx encoding of the tagged-message observer scenario described in
%% ODPOR with Observers (Aronis et al., TACAS 2018), Section 3.2.  This module
%% is not copied from the paper or from the Concuerror test suite.

main() ->
    R = self(),
    P = spawn(fun() -> R ! {b, self()}, R ! {a, self()} end),
    _Q = spawn(fun() -> R ! {a, self()} end),
    _S = spawn(fun() -> R ! {b, self()} end),
    receive {a, X} ->
        if X =:= P ->
            receive {b, Y} ->
                io:format("a=p b=~w~n", [Y])
            end;
           true ->
            io:format("a=q~n")
        end
    end.

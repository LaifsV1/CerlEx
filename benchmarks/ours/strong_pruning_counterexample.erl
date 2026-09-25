% Counterexample to the overly strong pruning rule:
%
%   if a same-sender-visible message matches, keep only same-sender-visible
%   receive branches.
%
% P sends {b,P} before {a,P}.  When the parent receives {a,P}, {b,P} becomes
% same-sender-visible by FIFO.  The second receive for {b,_} must not prune
% S's {b,S}: S is a different sender, and the current channel model does not
% record a global cross-sender mailbox order proving {b,S} is later than {b,P}.
%
% Expected with the current model:
%   CerlEx: 2 traces
%   Concuerror default: 2 interleavings
%   Concuerror --instant_delivery false: 2 interleavings
-module(strong_pruning_counterexample).
-export([test/0, p/1, s/1]).

test() ->
    Self = self(),
    P = spawn(?MODULE, p, [Self]),
    S = spawn(?MODULE, s, [Self]),
    receive
        {a, X} when X =:= P ->
            receive
                {b, Y} ->
                    case Y of
                        P -> p_first;
                        S -> s_first
                    end
            end
    end.

p(Parent) ->
    Parent ! {b, self()},
    Parent ! {a, self()}.

s(Parent) ->
    Parent ! {b, self()}.

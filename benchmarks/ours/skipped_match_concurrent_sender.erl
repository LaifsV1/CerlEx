%% Over-pruning witness for commit-clock pruning (vector_clocks_plan.md §2).
%%
%% {third,res} is sent after third commits go, but go was sent by main
%% *before* main's work-receive commit, so flag({first,res}) and
%% send({third,res}) are causally concurrent: in BEAM, {third,res} can be in
%% main's mailbox before {first,res}.  Both From = first and From = third are
%% real outcomes; the {third,res} receive branch must NOT be pruned.
-module(skipped_match_concurrent_sender).
-export([test/0, first/1, third/1]).

test() ->
    Self = self(),
    P3 = spawn(?MODULE, third, [Self]),
    P3 ! go,
    spawn(?MODULE, first, [Self]),
    receive
        work ->
            receive
                {From, res} ->
                    case From of
                        first -> ok;
                        third -> ok
                    end
            end
    end.

first(Parent) ->
    Parent ! {first, res},
    Parent ! work.

third(Parent) ->
    receive
        go -> Parent ! {third, res}
    end.

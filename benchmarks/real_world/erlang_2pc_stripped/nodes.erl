-module(nodes).
-export([test_commit/0, test_abort/0, coordinator/0, cohort/0]).

-record(coordinator_state, {decisions_basket}).
-record(cohort_state, {decision}).


coordinator() ->
    coordinator([], #coordinator_state{decisions_basket=[]}).

coordinator(Cohorts, #coordinator_state{decisions_basket = Basket} = State) ->
    receive
        {add_cohort, Pid} ->
            coordinator([Pid|Cohorts], State);
        {start_2pc_with_commit} ->
            query_to_commit(Cohorts), coordinator(Cohorts, State);
        {agreement, Agreement} ->
            NewBasket = [Agreement|Basket],
            VotingFinished = length(NewBasket) == length(Cohorts),
            case VotingFinished of
                true ->
                    completion(Cohorts, NewBasket);
                false ->
                    NewState = State#coordinator_state{decisions_basket=NewBasket},
                    coordinator(Cohorts, NewState)
            end
    end.

completion(Cohorts, Basket) ->
    Consensus = lists:all(fun(Agreement) -> Agreement == yes end, Basket),
    Action = case Consensus of
        true ->
            commit;
        false ->
            abort
    end,
    broadcast(Cohorts, {Action, self()}),
    wait_acknowledgements(length(Cohorts), Action).

wait_acknowledgements(0, _FinalState) ->
    ok;
wait_acknowledgements(RemainingCohortsNumber, FinalState) ->
    receive
        {acknowledgement} -> wait_acknowledgements(RemainingCohortsNumber - 1, FinalState)
    end.

cohort() ->
    cohort([], #cohort_state{decision=nil}).

cohort(Cohorts, State) ->
    receive
        {propose_decision, Decision} ->
            cohort(Cohorts, #cohort_state{decision=Decision});
        {query, Coordinator} ->
            Coordinator ! {agreement, State#cohort_state.decision},
            cohort(Cohorts, State);
        {commit, Coordinator} ->
            Coordinator ! {acknowledgement};
        {abort, Coordinator} ->
            Coordinator ! {acknowledgement}
    end.

query_to_commit(OtherNodes) ->
    broadcast(OtherNodes, {query, self()}).

broadcast(Nodes, Message) ->
    [Node ! Message || Node <- Nodes].

test_commit() ->
    A = spawn(nodes, coordinator, []),
    B = spawn(nodes, cohort, []),
    C = spawn(nodes, cohort, []),
    A ! {add_cohort, B},
    A ! {add_cohort, C},

    B ! {propose_decision, yes},
    C ! {propose_decision, yes},
    A ! {start_2pc_with_commit}.

test_abort() ->
    A = spawn(nodes, coordinator, []),
    B = spawn(nodes, cohort, []),
    C = spawn(nodes, cohort, []),
    A ! {add_cohort, B},
    A ! {add_cohort, C},

    B ! {propose_decision, yes},
    C ! {propose_decision, no},
    A ! {start_2pc_with_commit}.

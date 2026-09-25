-module(topology).
-export([dict_add/3, complete/1, ring/1, random/1, random_graph/1]).
-include_lib("eunit/include/eunit.hrl").

sequence(0) -> [];
sequence(N) -> [N | sequence(N-1)].

sequence_test() -> sequence(10).
sequence2_test() -> ?assert(length(sequence(10)) =:= 10).

complete(_, 0, D) -> D;
complete(Sequence, I, D) ->
  Val = lists : subtract(Sequence, [I]),
  ND = dict : append(I,  Val, D),
  complete(Sequence, I - 1, ND).

complete(N) ->
  D = dict : new(),
  S = sequence(N),
  complete(S, N, D).

ring(_, 0, D) -> D;
ring(N, I, D) ->
  Next = if I == N -> 1; true -> I + 1 end,
  ND = dict : append(I, [Next], D),
  ring(N, I-1, ND).

ring(N) ->
  D = dict : new(),
  ring(N,N,D).

random_sublist([X]) -> [X];
random_sublist([H  | T]) ->
  L = length([H | T]),
  X = rand : uniform(L),
  if
    (X >= L/2) -> random_sublist(T);
    true -> [H | random_sublist(T)]
  end.

random_graph_aux(_, 0, D) -> D;
random_graph_aux(Sequence, I, D) ->
  Val = random_sublist(lists : subtract(Sequence, [I])),
  ND = dict : append(I,  Val, D),
  random_graph_aux(Sequence, I - 1, ND).

random_graph(N) ->
  D = dict : new(),
  S = sequence(N),
  random_graph_aux(S, N, D).

dict_add(Key, Elt, Graph) ->
  F = dict : find(Key, Graph),
  case F of
    {ok, [V]} ->
      Res = lists : member(Elt, V),
      if
	Res == true -> Graph;
	true ->
	 dict : append(Key, [Elt | V], dict : erase(Key, Graph))
      end;
   _ -> dict : append(Key, [Elt], Graph)
  end.

sym(Graph) ->
  F = fun(Key, Value, AccIn) ->
    [V] = Value,
    G = fun(Elt, AccList) ->
      AccListTmp = dict_add(Key, Elt, AccList),
      dict_add(Elt, Key, AccListTmp)
    end,
    lists : foldl(G, AccIn, V)
  end,
  dict : fold(F, dict : new(), Graph).

random(N) ->
  G = random_graph(N),
  sym(G).

%% Test harness written for CerlEx — not part of the original ring-leader-election project.
%% Runs Chang-Roberts LCR in a ring of 3 processes with UIDs 1, 2, 3 (process 3 wins).
-module(main).
-export([main/0]).

main() ->
    N = 3,
    Graph = topology:ring(N),
    {_S, B} = control:init(lcr, N, Graph, fun(X) -> X end),
    B(start).

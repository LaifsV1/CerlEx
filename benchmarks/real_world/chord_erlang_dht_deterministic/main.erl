%% Test harness written for CerlEx — not part of the original chord_erlang_dht project.
%% Tests concurrent ring joins (alpha, beta, gamma), put/get routing to each node,
%% and peer departure (alpha stops, ring contracts to beta and gamma).  Names
%% and resources are strings so helper:hash/1 can compute the same keys on any
%% Erlang implementation.
-module(main).
-export([main/0]).

main() ->
    P1 = chord_peer:add("alpha"),
    P2 = chord_peer:add("beta", P1),
    P3 = chord_peer:add("gamma", P1),
    P1 ! {put, "file1"},
    P2 ! {put, "file2"},
    P3 ! {put, "file3"},
    P1 ! {get, "file1"},
    P2 ! {get, "file2"},
    P3 ! {get, "file3"},
    P1 ! stop.

-module(prefix_reuse_4).
-export([main/0, echo/1, worker/2]).

%% Deliberate counterweight to alltoall6/alltoall7 (notes/network_experiments.md,
%% the computation-tree columns).  Those are wide-and-shallow, so online
%% exploration pays for speculation it cannot amortise.  This family is the
%% mirror image: a long DETERMINISTIC chain of schedule points shared by every
%% real trace, then a 4-way race at the end.
%%
%% Stateless replay re-derives the whole 40-round chain once per real trace;
%% the online tree builds it once.  The ratio is bounded by the number of
%% traces sharing the prefix, so the family grows in our favour with the
%% width of the tail, not the length of the chain:
%%   workers=3   6 traces    5.25x
%%   workers=4  24 traces   14.07x
%%   workers=5 120 traces   25.42x
%% (measured 2026-09-21 with -prefix-stats; chain length alone asymptotes at
%% the trace count -- 3.23x at chain=5 up to 5.59x at chain=80 with workers=3.)
%%
%% Note the chain must be built from SCHEDULE POINTS, not computation: a long
%% deterministic calculation runs inside one maximise step and creates no
%% configurations, so it is invisible to the metric (burn(0) through
%% burn(30000) before the same race all measure 16 online / 24 stateless).

main() ->
    S = self(),
    E = spawn(?MODULE, echo, [40]),
    chain(E, 40),
    spawn(?MODULE, worker, [S, w1]),
    spawn(?MODULE, worker, [S, w2]),
    spawn(?MODULE, worker, [S, w3]),
    spawn(?MODULE, worker, [S, w4]),
    receive _ -> ok end,
    receive _ -> ok end,
    receive _ -> ok end,
    receive _ -> ok end.

chain(_, 0) -> ok;
chain(E, N) ->
    E ! {self(), ping},
    receive pong -> ok end,
    chain(E, N - 1).

echo(0) -> ok;
echo(N) ->
    receive {P, ping} -> P ! pong end,
    echo(N - 1).

worker(P, T) -> P ! T.

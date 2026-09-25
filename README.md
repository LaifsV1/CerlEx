# CerlEx
![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)

CerlEx explores the interleavings of concurrent [Core Erlang](https://www.it.uu.se/research/group/hipe/cerl/)
programs.  It is the prototype accompanying *Observation-Directed Trace
Exploration*.

Rather than replaying a schedule from the initial state for each alternative,
CerlEx retains program states and keeps the merge of per-sender message
streams unresolved inside a single configuration.  A selective receive
branches only on the messages it can actually distinguish, so message-order
distinctions are enumerated when a program observation demands one.

## Build

Requires OCaml (dune, zarith) and Erlang/OTP for `erlc`.

```
dune build
```

## Use

```
dune exec cerlex -- -e program.core                    # explore
dune exec cerlex -- -e program.core -entry mod:fun     # choose the entry point
dune exec cerlex -- -i program.core                    # evaluate a single process
```

Compile Erlang sources to Core with `erlc +to_core foo.erl`.  Modules that use
`lists`, `string` or `dict` need the matching file from `otp_stdlib/` passed
after the program.

Useful flags: `-quiet` (suppress per-trace output), `-no-io` (suppress the
program's own output), `-bfs`, `-memo N`, `-prefix-stats` (report the
computation tree), and `-no-fo` (disable forced-order checking, which makes
the counts over-approximate and exists only for A/B measurement).

## Experiments

```
bash run_experiments.sh > EXPERIMENTS.md
bash run_experiments.sh --concuerror > EXPERIMENTS.md   # also runs Concuerror
```

`EXPERIMENTS.md` is the generated table.  It covers 61 message-passing entry
points in `benchmarks/`:

- `benchmarks/concuerror/` — the pure message-passing entries of
  [Concuerror](https://concuerror.com)'s test suite.
- `benchmarks/real_world/` — three Erlang programs taken from public
  repositories: a Chord distributed hash table, a two-phase commit protocol,
  and Chang--Roberts ring leader election, with output-free variants.  These
  were written to be used rather than to exercise a model checker.  See the
  paper for sources.
- `benchmarks/ours/` — written for this work, including two families designed
  to be adversarial in opposite directions: `alltoall*`, where every process
  sends to every other before any receives, and `prefix_reuse_*`, where many
  traces share a long deterministic prefix.

Each row reports what CerlEx explored and a same-tree *replay* counterfactual:
the work a stateless explorer would repeat if it re-derived every real trace
from the initial state.  That baseline isolates the effect of retaining
prefixes; it is not a cost model of any existing tool.

## Licence

CerlEx is released under the MIT licence (`LICENSE`), except for two
directories that remain under the Apache License 2.0:

- `lib/core_syntax`, adapted from the Core Erlang frontend of
  [Caramel](https://github.com/leostera/caramel) (`lib/core_syntax/LICENSE`);
- `otp_stdlib`, the `lists`, `string` and `dict` modules of
  [Erlang/OTP](https://github.com/erlang/otp), Copyright Ericsson AB
  (`otp_stdlib/LICENSE`).

Files changed for CerlEx say so in their headers.

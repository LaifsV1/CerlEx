# Core Erlang

This directory contains a subset of the Core Erlang-related files from the
`erlang` library distributed as part of the Caramel repository:

<https://github.com/leostera/caramel/tree/main/erlang>

The original `erlang` subproject in Caramel is licensed under the Apache
License 2.0. A copy of the relevant license text is included in this directory.

### Dependencies: 
```
opam
ocaml
dune
menhir
sexplib
ppx_sexp_conv
```

This directory includes only the subset needed for Core Erlang parsing,
representation, and printing, rather than the full original `erlang` library.

---

The section below is adapted from the original Caramel `erlang` README.

## Core Erlang

This library contains:

- a definition of an AST for Core Erlang,
- a parser that follows the [Core Erlang Spec](https://web.archive.org/web/20111211153744/https://www.it.uu.se/research/group/hipe/cerl/doc/core_erlang-1.0.3.pdf), and
- 2 printers: a debugging S-expression printer and a Core Erlang printer.
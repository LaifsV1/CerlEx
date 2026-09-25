(lang dune 3.11)
(name cerlex)
(authors "Yu-Yang Lin")
(maintainers "linhouy@tcd.ie")
(license MIT Apache-2.0)
(generate_opam_files true)
(using menhir 2.1)

(package
 (name cerlex)
 (synopsis "An interleaving exploration tool for concurrent Core Erlang programs")
 (description
  "CerlEx explores the message interleavings of concurrent Core Erlang
   programs, retaining program states rather than replaying schedules from
   the initial state.  Its Core Erlang frontend is adapted from Caramel."))
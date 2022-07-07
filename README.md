# Aneris
[![CI](https://github.com/logsem/aneris/workflows/CI/badge.svg?branch=master)](https://github.com/logsem/aneris/actions?query=workflow%3ACI)

Aneris is a higher-order distributed concurrent separation logic for developing
and verifying distributed systems with facilities for modular specification and
verification of partial correctness properties and refinement. The logic is
built using the [Iris](https://iris-project.org) program logic framework and
mechanized in the [Coq proof assistant](https://coq.inria.fr/).

## Dependencies

Install Coq version 8.15.1.
If you have opam, this can be done with `opam install coq.8.15.1`.
If you do not have opam, it should be available through your package manager of choice.
See more at [https://opam.ocaml.org/doc/Install.html](https://opam.ocaml.org/doc/Install.html).

## Compiling

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`aneris/`](aneris/): The Aneris instantiation of Trillium
  * [`examples/reliable_communication`](aneris/examples/reliable_communication):
    for the AnerisLang implementation and Aneris verification of the reliable communication components

- [`fairness/`](fairness/): A HeapLang instantiation of Trillium for reasoning
  about fair termination of concurrent programs.
  
- [`ml_sources/`](ml_sources/): The Multicore OCaml source files 
  * [`aneris_lang/`](ml_sources/aneris_lang/): for the shim and the implementation of libraries related to the [`aneris/`](aneris/) folder
  * [`examples/reliable_communication`](ml_sources/examples/reliable_communication): for the OCaml implementation of the reliable communication components

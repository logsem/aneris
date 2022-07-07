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
  
- [`ml_sources/`](ml_sources/): The Multicore OCaml source files 
  * [`aneris_lang/`](ml_sources/aneris_lang/): for the shim and the implementation of libraries related to the [`aneris/`](aneris/) folder
  * [`examples/reliable_communication`](ml_sources/examples/reliable_communication): for the OCaml implementation of the reliable communication components

## Differences from the paper

# No initial component-specific resources.

The specifications are defined in terms of primitive Aneris resources, rather
than the initial component-specific resources presented in the paper.
We plan to resolve this discrepancy in the future

# Typeclasses as a means of the dependent specification pattern

The so-called dependent specification pattern of the paper is a simplification
of the mechanised abstraction, for presentation purposes.
In the mechanisation we achieve the abstract specifications by using typeclasses,
which carry the user parameters and abstract resources.
These are implicitly provided to the specifications which, in some cases, require
us to provide them explicitly, as Coq cannot automatically unify the correct typeclass.

# Auxilliary arguments in the user parameters and resources 

Some of the specifications carry more parameters than presented in the paper.
One particular parameter is the internal `namespace` of the reliable communication library,
which is then required in all of the components built on top of it.
We conjecture that this parameter can be hidden, and so we have not included it in the paper.

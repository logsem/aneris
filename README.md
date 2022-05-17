# Aneris
[![CI](https://github.com/logsem/aneris/workflows/CI/badge.svg?branch=master)](https://github.com/logsem/aneris/actions?query=workflow%3ACI)

Aneris is a higher-order distributed concurrent separation logic for developing
and verifying distributed systems with facilities for modular specification and
verification of partial correctness properties and refinement. The logic is
built using the [Iris](https://iris-project.org) program logic framework and
mechanized in the [Coq proof assistant](https://coq.inria.fr/).

## Compiling

The project maintains compatibility with Coq 8.15 and relies on `coqc` being
available in your shell. Next, clone the external submodule dependencies using

    git submodule update --init --recursive

Alternatively, clone the repository using the `--recurse-submodules` flag.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Updating git submodule dependencies

To pull the latest git submodule dependencies as committed to the repository, run

    git submodule update --recursive

By default, the `git pull` command recursively fetches submodule
changes. However, it does not apply the changes. To update the dependencies run

    git submodule update --recursive --remote

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`aneris/`](aneris/): The Aneris instantiation of Trillium
  * [`examples/`](aneris/examples/): example uses and verification case studies

- [`fairness/`](fairness/): A HeapLang instantiation of Trillium for reasoning
  about fair termination of concurrent programs.
  
- [`ml_sources/`](ml_sources/): The Multicore OCaml source files 
  * [`aneris_lang/`](ml_sources/aneris_lang/): for the [`aneris/`](aneris/) OCaml shim and lib files
  * [`examples/`](ml_sources/examples/): for the implementaiton of examples 

## Compiling from OCaml sources

To automatically generate AnerisLang programs from Ocaml source files, pin the `ocaml2lang` package:

    opam pin git+https://github.com/leon-gondelman/ocaml2lang#multicore


This will produce an executable `o2a`. After installation succeeds, you can try `o2a` by doing

    o2a --h

    
You can now run at the root of the repository

    o2a --rewrite
    
to generate Coq files just for the examples.

To compile ocaml sources, just run 

    dune build 
    
at the root of the repository.

## Publications

Aneris was initially presented in the ESOP 2020 paper [Aneris: A Mechanised
Logic for Modular Reasoning about Distributed
Systems](https://iris-project.org/pdfs/2020-esop-aneris-final.pdf) by Morten
Krogh-Jespersen, [Amin Timany](https://cs.au.dk/~timany/), Marit Edna
Ohlenbusch, [Simon Oddershede Gregersen](https://cs.au.dk/~gregersen/), and
[Lars Birkedal](https://cs.au.dk/~birke/). Since then, the duplicate protection
assumption as described in the paper has been relaxed.

At POPL 2022, a formal specification and verification of causally-consistent
distributed key-values store using Aneris was presented in the paper
[Distributed Causal Memory: Modular Specification and Verification in
Higher-Order Distributed Separation
Logic](https://iris-project.org/pdfs/2021-popl-ccddb-final.pdf) by [Leon
Gondelman](https://cs.au.dk/~gondelman/), [Simon Oddershede
Gregersen](https://cs.au.dk/~gregersen/), [Abel
Nieto](https://abeln.github.io/), [Amin Timany](https://cs.au.dk/~timany/), and
[Lars Birkedal](https://cs.au.dk/~birke/). This development is available in the
[aneris/examples/ccddb](aneris/examples/ccddb) folder.

A [preprint](https://iris-project.org/pdfs/2021-submitted-trillium.pdf) is
available describing Trillium, a program logic framework for both proving
partial correctness properties and trace properties; Aneris is now an
instantiation of the Trillium framework.

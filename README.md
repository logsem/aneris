# Aneris
[![CI](https://github.com/logsem/aneris/workflows/CI/badge.svg?branch=master)](https://github.com/logsem/aneris/actions?query=workflow%3ACI)

Aneris is a higher-order distributed concurrent separation logic for developing
and verifying distributed systems with facilities for modular specification and
verification of partial correctness properties and refinement. The logic is
built using the [Iris](https://iris-project.org) program logic framework and
mechanized in the [Coq proof assistant](https://coq.inria.fr/).

Recent documentation of Aneris is available [`here`](documentation.pdf). 

## Compiling

The project maintains compatibility with Coq 8.18 and relies on `coqc` being
available in your shell. Clone the external git submodule dependencies using

    git submodule update --init --recursive

Alternatively, clone the repository using the `--recurse-submodules` flag.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`aneris/`](aneris/): The Aneris instantiation of Trillium
  * [`examples/`](aneris/examples/): examples and case studies

- [`fairness/`](fairness/): A HeapLang instantiation of Trillium for reasoning
  about fair termination of concurrent programs.

- [`ml_sources/`](ml_sources/): The Multicore OCaml source files
  * [`aneris_lang/`](ml_sources/aneris_lang/): shim and aneris libraries
  * [`examples/`](ml_sources/examples/): examples and case studies

## Git submodule dependencies

This project uses git submodules to manage dependencies with other Coq
libraries. By default, when working with a repository that uses submodules, the
submodules will *not* be populated and updated automatically, and it is often
necessary to invoke `git submodule update --init --recursive` or use the
`--recurse-submodules` flag. However, this can be automated by setting the
`submodule.recurse` setting to `true` in your git config by running

    git config --global submodule.recurse true

This will make `git clone`, `git checkout`, `git pull`, etc. work as you would
expect and it should rarely be necessary to invoke any `git submodule update`
commands.

A git submodule is pinned to a particular commit of an external (remote)
repository. If new commits have been pushed to the remote repository and you
wish to integrate these in to the development, invoke

    git submodule update --remote

to fetch the new commits and apply them to your local repository. This changes
which commit your *local* submodule is pinned to. Remember to commit and push
the submodule update to make it visible to other users of the repository.

Read more about git submodules in [this
tutorial](https://git-scm.com/book/en/v2/Git-Tools-Submodules).

## Compiling from OCaml sources

To generate AnerisLang programs from OCaml source files, pin the `ocaml2lang` package:

    opam pin git+https://github.com/leon-gondelman/ocaml2lang#multicore

This will produce an executable `o2a`. After installation succeeds, you can try `o2a` by doing

    o2a --help

You can now run

    o2a --rewrite

at the root of the repository to generate Coq files from the OCaml sources in
[`ml_sources`](/ml_sources). To compile the source files, run

    dune build --root .

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

[Trillium](https://iris-project.org/pdfs/2024-popl-trillium.pdf) 
is a program logic framework for both proving
partial correctness properties and trace properties; Aneris is now an
instantiation of the Trillium framework.

Aneris also supports trace-based reasoning to establish free theorems using the 
the method described in [Theorems for Free from Separation Logic Specifications](https://iris-project.org/pdfs/2021-icfp-intensional-final.pdf). 
In fact, parts of the Coq development accompaying the paper 
are injected into the Aneris program logic. 
For completeness, this concerns elements in the files: 

- aneris/aneris_lang/ast.v
- aneris/aneris_lang/lang.v 
- aneris/aneris_lang/resources.v
- aneris/aneris_lang/adequacy.v 
- aneris/aneris_lang/lifting.v
- aneris/aneris_lang/resources.v
- aneris/aneris_lang/state_interp/state_interp_def.v
- aneris/aneris_lang/adequacy_trace.v
- aneris/aneris_lang/program_logic/aneris_lifting.v

# Aneris
[![Build Status](https://travis-ci.com/logsem/aneris.svg?token=rjT7z1yqWrMesq694bBy&branch=master)](https://travis-ci.com/logsem/aneris)

Aneris is a programming language and a higher-order distributed concurrent
separation logic for developing and verifying distributed systems with
facilities for modular specification and verification of partial correctness
properties. The logic is built using the [Iris](https://iris-project.org)
program logic framework and mechanized in the Coq proof assistant.

## Compiling

To install the dependencies, you have to add the following opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `opam update` followed by `make build-dep` to
install the right versions of the dependencies as specified in the `aneris.opam`
file.

Next, clone the external submodule dependencies using

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

Remember to commit submodule updates to the repository.

## Publications

Aneris was initially presented in the ESOP 2020 paper [Aneris: A Mechanised
Logic for Modular Reasoning about Distributed
Systems](https://link.springer.com/chapter/10.1007/978-3-030-44914-8_13) by
Morten Krogh-Jespersen, [Amin Timany](https://tildeweb.au.dk/au571806/), Marit
Edna Ohlenbusch, [Simon Oddershede Gregersen](https://cs.au.dk/~gregersen/), and
[Lars Birkedal](https://cs.au.dk/~birke/). Since then, the duplicate protection
assumption as described in the paper has been relaxed.

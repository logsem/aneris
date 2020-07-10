# Aneris Logic

Aneris is a program logic build on the Iris program logic framework for
developing and verifying distributed systems.

## Compiling

The development is known to compile with

- `coq`: version `8.11.2`
- `coq-iris` : see the `opam` file
- `coq-stdpp` : see the `opam` file
- `coq-iris-string-ident`

To install the dependencies, you have to add the following opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `opam update` followed by `make build-dep` to
install the right versions of the dependencies.

Next, clone external submodule dependencies using

    git submodule update --init --recursive

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Directory Structure

## Case studies

- Causally-consistent distributed database

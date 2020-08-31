# Aneris

Aneris is a program logic build on the Iris program logic framework for
developing and verifying distributed systems.

## Compiling

The development is known to compile with

- `coq`: see the `opam` file
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

Alternatively, clone the repository using the `--recurse-submodules` flag.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Updating dependencies

By default, the `git pull` command recursively fetches submodule
changes. However, it does not apply the changes. To apply the submodule updates
you need to run

    git submodule update --recursive --remote

Remember to commit submodule updates to the repository.

## Directory structure

TODO

## Case studies

See [aneris-examples](https://bitbucket.org/logsem/aneris-examples).

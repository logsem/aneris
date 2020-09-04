ARG coq_image="coqorg/coq:dev"
FROM ${coq_image}

LABEL maintainer="gregersen@cs.au.dk"

RUN eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
    opam repository add --all-switches --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
    && opam update -y -u \
    && opam config list && opam repo list && opam list \
    && opam clean -a -c -s --logs

COPY --chown=coq:coq . /coq
WORKDIR /coq
ENV OPAMYES true

RUN make build-dep
RUN make -j ${NJOBS}

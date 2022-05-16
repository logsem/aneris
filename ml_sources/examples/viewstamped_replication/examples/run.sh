#!/bin/bash


EXE="~/repositories/aneris/aneris-examples/_build/default/ml_sources/viewstamped_replication/examples/observe_par_sc2.exe"

RUN () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"} ${1//\"/\\\"} ${2//\"/\\\"}"'"'
}

cd ~/repositories/aneris/aneris-examples

dune build

cd ~/repositories/aneris/aneris-examples/ml_sources/viewstamped_replication/examples

RUN r4
RUN r3
RUN r2
RUN r1
RUN r0
RUN cl

#!/bin/bash


EXE="~/repositories/aneris/toolO2A/ocaml2lang/_build/default/test/aneris_examples/ml_sources/consensus/paxos_runner.exe"

RUN () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"} ${1//\"/\\\"}"'"'
}

RUN_PROPOSER () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"} ${1//\"/\\\"} ${2//\"/\\\"}"'"'
}


RUN a1
RUN a2
RUN a3
RUN_PROPOSER p1 13
RUN_PROPOSER p2 42
RUN c
RUN l1
RUN l2

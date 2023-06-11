#!/bin/bash


EXE="~/research/aneris/ml_sources/_build/default/examples/snapshot_isolation/examples/anomalies/anomalie_1/anomalie_1_runner.exe"

RUN () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"} ${1//\"/\\\"} ${2//\"/\\\"}"'"'
}

cd ~/research/aneris/ml_sources

dune build

cd ~/research/aneris/ml_sources/examples/snapshot_isolation/examples/anomalies/anomalie_1/

RUN 0;
RUN 1;
RUN 2;
RUN 3;
RUN 4;

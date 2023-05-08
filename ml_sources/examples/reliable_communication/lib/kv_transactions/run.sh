#!/bin/bash


EXE=".../Aneris/aneris/_build/default/ml_sources/examples/reliable_communication/lib/kv_transactions/examples_runner.exe"

RUN () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"}"'"'
}

RUN
#!/bin/bash


EXE="~/repositories/portal/aneris-examples/_build/default/ml_sources/reliable_communication/examples/messages_in_order/messages_in_order_runner.exe"

RUN () {
   osascript -e 'tell app "Terminal" to do script "'"${EXE//\"/\\\"} ${1//\"/\\\"} ${2//\"/\\\"}"'"'
}

cd ~/repositories/portal/aneris-examples/

dune build

cd ~/repositories/portal/aneris-examples/ml_sources/reliable_communication/examples/messages_in_order/

RUN clt
RUN srv

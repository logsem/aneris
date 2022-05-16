From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import set_code.
From aneris.examples.transaction_commit Require Import two_phase_code.

Definition runner : expr :=
  let: "TM"  := MakeAddress #"tm" #80 in
  let: "RM1" := MakeAddress #"rm.01" #80 in
  let: "RM2" := MakeAddress #"rm.02" #80 in
  let: "RM3" := MakeAddress #"rm.03" #80 in
  let: "RMs" := {[ "RM1"; "RM2"; "RM3" ]} in
  Start "rm.01" (resource_manager "RM1" "TM");;
  Start "rm.02" (resource_manager "RM2" "TM");;
  Start "rm.03" (resource_manager "RM3" "TM");;
  Start "tm" (transaction_manager "TM" "RMs").

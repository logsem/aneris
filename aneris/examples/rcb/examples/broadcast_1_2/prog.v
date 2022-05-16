From aneris.aneris_lang.lib.serialization Require Import serialization_code serialization_proof.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.rcb Require Import spec.

Definition op_ser := int_ser.
Definition op_deser := int_deser.

Definition broadcast_1_2 : val :=
  λ: "broadcast",
    "broadcast" #1 ;;
    "broadcast" #2.

Definition deliver_1_2 : val :=
  λ: "deliver",
    let: "m" := wait_deliver "deliver" #() in
    let: "x" := Fst (Fst "m") in
    assert: ("x" = #1) ;;
    let: "m" := wait_deliver "deliver" #() in
    let: "x" := Fst (Fst "m") in
    assert: ("x" = #2).

Definition z0 := SocketAddressInet "0.0.0.0" 80.
Definition z1 := SocketAddressInet "0.0.0.1" 80.

Program Instance myparams : RCB_params :=
{|
  RCB_addresses := [z0; z1];
  RCB_InvName := nroot .@ "rcbinv";
  RCB_serialization := int_serialization;
|}.
Next Obligation.
  repeat constructor; set_solver.
Qed.

Section Main.
  Context `{RCB_init_function}.

  Definition main : expr :=
    Start "0.0.0.0"
      (let: "deliver_broadcast" := init $RCB_addresses #0 in 
       let: "broadcast" := Snd "deliver_broadcast" in
       broadcast_1_2 "broadcast") ;;
    Start "0.0.0.1"
      (let: "deliver_broadcast" := init $RCB_addresses #1 in
       let: "deliver" := Fst "deliver_broadcast" in
       deliver_1_2 "deliver").
End Main.

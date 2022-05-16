From aneris.aneris_lang Require Import lang network.
From aneris.examples.ccddb.spec Require Import base init.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Definition z0 := SocketAddressInet "0.0.0.0" 80.
Definition z1 := SocketAddressInet "0.0.0.1" 80.
Definition dbs : val := InjRV (#z0, (InjRV (#z1, InjLV #()))).

Section Node0.
  Context `{!DB_init_function}.

  Definition z0_prog : expr := λ: "wr",
    "wr" #"x" #37;;
    "wr" #"y" #1.

  Definition z0_node : expr :=
    λ: "dbs",
      let: "p" := init "dbs" #0 in
      let: "rd" := Fst "p" in
      let: "wr" := Snd "p" in
      z0_prog "wr".

End Node0.

Section Node1.

  Context `{!DB_init_function}.

  Definition z1_prog : expr := λ: "rd",
    repeat_read_until "rd" #"y" #1;;
    let: "r" := "rd" #"x" in
    assert: "r" = SOMEV #37;;
    "r".

  Definition z1_node : expr :=
    λ: "dbs",
      let: "p" := init "dbs" #1 in
      let: "rd" := Fst "p" in
      let: "wr" := Snd "p" in
      z1_prog "rd".

End Node1.

Section Main.

  Context `{!DB_init_function}.

  Definition main : expr :=
    Start "0.0.0.0" (z0_node dbs) ;;
    Start "0.0.0.1" (z1_node dbs).

End Main.

Program Instance myparams : DB_params :=
  {| DB_addresses := [z0; z1];
     DB_keys := {["x"; "y"]};
     DB_InvName := nroot .@ "dbinv";
     DB_serialization := int_serialization;
  |}.
Next Obligation.
  repeat constructor; set_solver.
Qed.

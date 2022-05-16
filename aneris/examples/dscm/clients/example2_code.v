From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import par_code.
From aneris.examples.dscm Require Import base.

Definition thread (init : val) (sa : socket_address) (k : Key) (n : Z) : val :=
  λ: "dbs",
    let: "p" := init #sa "dbs" in
    let: "rd" := Fst "p" in
    let: "wr" := Snd "p" in
    "wr" #k #n;; "rd" #k.

Definition prog (init : val) (sa1 sa2 : socket_address) (k : Key) (n1 n2 : Z) : val :=
  λ: "dbs",
    ( thread init sa1 k n1 "dbs" ||| thread init sa2 k n2 "dbs" ).

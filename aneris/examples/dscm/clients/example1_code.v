From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import par_code.

Definition par_prog : expr :=
  λ: "wr" "rd",
    "wr" #"x" #0;;
    "wr" #"y" #0;;
    ("wr" #"x" #1;; "rd" #"y") ||| ("wr" #"y" #1;; "rd" #"x" ).

Definition init_prog (init : val) (sa : socket_address) : expr :=
  λ: "dbs",
    let: "p" := init "dbs" #sa in
    let: "rd" := Fst "p" in
    let: "wr" := Snd "p" in
    par_prog "wr" "rd".

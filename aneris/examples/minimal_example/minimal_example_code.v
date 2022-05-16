From aneris.aneris_lang Require Import ast.

Definition incr_loop : val :=
  rec: "incr_loop" "l" :=
    let: "n" := !"l" in
    CAS "l" "n" ("n" + #1);;
        "incr_loop" "l".

Definition incr_example : expr :=
  let: "l" := ref<<"s">> #0 in
  Fork (incr_loop "l");; incr_loop "l".

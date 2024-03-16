From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.transactional_consistency Require Import code_api.

Section GenericWait. 

  Context `{!KVS_transaction_api}.

  Definition commitU : val := λ: "cst", let: "_b" := TC_commit "cst" in
                                       #().

  Definition wait_transaction : val :=
    λ: "cst" "cond" "k",
    TC_start "cst";;
    letrec: "aux" <> :=
      match: TC_read "cst" "k" with
        NONE => "aux" #()
      | SOME "v" =>
          (if: "cond" "v"
          then  commitU "cst"
          else  "aux" #())
      end in
      "aux" #().

End GenericWait.
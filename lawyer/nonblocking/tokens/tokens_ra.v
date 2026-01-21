From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmultiset.
From heap_lang Require Import lang.


Class MethodTokenPre (Σ: gFunctors) := {
    (* mt_pre_tok :: inG Σ (exclR positive); *)
}.
Class MethodToken (MS: gmultiset val) (Σ: gFunctors) := {
    (* ut_pre_pre :: MethodTokenPre Σ; *)
    mt_γ: gname;
}.


(* TODO: generalize, upstream *)
Section TokensRA.
  Context `{MethodToken MS Σ}.
  
  Definition methods_toks (ms: gmultiset val): iProp Σ. Admitted.

  (* Global Instance is_op_mt m1 m2 :  *)
  (*   IsOp (methods_toks (m1 ⊎ m2)) (methods_toks m1) (methods_toks m2). *)
  (* Proof. by rewrite /IsOp' /IsOp frac_op Qp.div_2. Qed. *)

  Global Instance methods_toks_tl ms: Timeless (methods_toks ms).
  Proof using. Admitted.

  Lemma methods_toks_split ms1 ms2:
    methods_toks (ms1 ⊎ ms2) ⊣⊢ methods_toks ms1 ∗ methods_toks ms2.
  Proof using. Admitted.

  Lemma methods_toks_sub ms:
    methods_toks ms -∗ ⌜ ms ⊆ MS ⌝.
  Proof using. Admitted. 

  Definition method_tok (m: val) := methods_toks {[+ m +]}. 

  Lemma method_tok_sub m:
    method_tok m -∗ ⌜ m ∈ MS ⌝.
  Proof using.
    rewrite -gmultiset_singleton_subseteq_l. 
    iApply methods_toks_sub.
  Qed.  

End TokensRA.

Lemma mt_init `{MethodTokenPre Σ} MS:
  ⊢ ∃ (MT: MethodToken MS Σ), methods_toks MS.
Proof using. Admitted.

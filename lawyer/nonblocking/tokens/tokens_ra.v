From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmultiset auth.
From heap_lang Require Import lang.


Class MethodTokenPre (Σ: gFunctors) := {
    mt_pre_tok :: inG Σ (authR (gmultiset val));
}.
Class MethodToken (MS: gmultiset val) (Σ: gFunctors) := {
    mt_pre :: MethodTokenPre Σ;
    mt_γ: gname;
}.

Definition mt_Σ: gFunctors := #[GFunctor $ authR (gmultiset val)].
Global Instance mt_sub: forall Σ, subG mt_Σ Σ -> MethodTokenPre Σ.
Proof using. solve_inG. Qed.


(* TODO: generalize, upstream? *)
Section TokensRA.
  Context `{MethodToken MS Σ}.
  
  Definition methods_toks (ms: gmultiset val): iProp Σ :=
    own mt_γ (●{DfracDiscarded} MS ⋅ ◯ ms).    

  Lemma methods_toks_split ms1 ms2:
    methods_toks (ms1 ⊎ ms2) ⊣⊢ methods_toks ms1 ∗ methods_toks ms2.
  Proof using.
    rewrite /methods_toks. rewrite -own_op.
    apply own_proper.
    rewrite -gmultiset_op. rewrite auth_frag_op.
    rewrite !cmra_assoc. apply cmra_op_proper'; [| done].
    rewrite cmra_comm. rewrite -cmra_assoc. apply cmra_op_proper'; [done| ].
    rewrite -auth_auth_dfrac_op. by rewrite dfrac_op_discarded.
  Qed.

  Lemma methods_toks_sub ms:
    methods_toks ms -∗ ⌜ ms ⊆ MS ⌝.
  Proof using.
    rewrite /methods_toks. iIntros "X".
    iDestruct (own_valid with "X") as %V. iPureIntro.
    apply auth_both_dfrac_valid_discrete in V.
    rewrite gmultiset_included in V. apply V.
  Qed.

  Definition method_tok (m: val) := methods_toks {[+ m +]}. 

  Lemma method_tok_sub m:
    method_tok m -∗ ⌜ m ∈ MS ⌝.
  Proof using.
    rewrite -gmultiset_singleton_subseteq_l. 
    iApply methods_toks_sub.
  Qed.  

End TokensRA.

Lemma mt_init `{MethodTokenPre Σ} MS:
  ⊢ |==> ∃ (MT: MethodToken MS Σ), methods_toks MS.
Proof using.
  iStartProof. 
  iMod (own_alloc (●{DfracDiscarded} MS ⋅ ◯ MS)) as (γ) "X".
  { apply auth_both_dfrac_valid_2; done. }
  iExists {| mt_γ := γ |}. by iFrame.
Qed.

From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From trillium.fairness Require Import fuel lm_fair.
From trillium.fairness.lm_rules Require Import resources_updates.


(* TODO: move *)
Section EGN.
  Context {M: FairModel} `{Countable G}. 
  Let R := fmrole M.

  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}.
  Let LMF := LM_Fair (LF := LF).

  Definition enabled_group_nonempty g δ :=
    role_enabled_model (g: fmrole LMF) δ <->
    default ∅ (ls_tmap δ !! g) ≠ ∅. 
  

  Section EGNProperties.
    Context `{EGN: forall g δ, enabled_group_nonempty g δ}.

    Lemma enabled_group_nonempty_neg g δ:
      ¬ role_enabled_model (g: fmrole LMF) δ <->
        default ∅ (ls_tmap δ !! g) = ∅.
    Proof.
      pose proof (EGN g δ) as E. red in E. tauto.
    Qed.       

  End EGNProperties.

End EGN.

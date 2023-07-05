From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang Require Import simulation_adequacy. 
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From stdpp Require Import finite.
From trillium.fairness Require Import fairness_finiteness.

Import derived_laws_later.bi.

From trillium.fairness.examples.spinlock Require Import spinlock_sc_comp_pmp spinlock_sc_adequacy spinlock_sc_comp spinlock_sc_comp_model. 


Section CompRA.
    
  Definition compΣ : gFunctors :=
    gFunctors.app (GFunctor comp_cmra) (gFunctors.app spinlockΣ spinlockΣ).
    (* gFunctors.app (GFunctor comp_cmra) spinlockΣ. *)
  
  Global Instance subG_compΣ {Σ}:
    subG compΣ Σ → compPreG Σ.
  Proof. solve_inG. Qed.

End CompRA.

Instance comp_proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in comp_trans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

(* TODO: not true so far! need to restrict init step of comp model *)
Lemma comp_model_finitary (s: comp_model_impl):
  Finite { '(s', ℓ) | comp_trans s ℓ s'}.
Proof.  
  destruct s as ((os1, os2), osc). simpl.
  set (get_sl_steps := fun os => from_option (fun s => proj1_sig <$> (@enum _ _ (spinlock_model_finitary s))) nil os). 
  (* set (steps1 := (fun '(s: , oρ) => (((Some s, os2, osc): spinlock_sc.spinlock_model_impl), *)
  (*                                match oρ with *)
  (*                                | Some ρ => (Some $ inl $ inl ρ) *)
  (*                                | None => None *)
  (*                                end)) *)
  (*                                <$> get_sl_steps os1).  *)
  (* set (steps2 := get_sl_steps os2).  *)
  (* from_option (live_roles _) ∅ s *)
Admitted. 

Lemma comp_model_term (mtr: mtrace comp_model_impl): mtrace_fairly_terminating mtr.
Proof.
  red. intros VALID FAIR. 
  destruct (infinite_or_finite mtr) as [INF | ?]; [| done]. exfalso.
  (* inr transitions are well-founded. *)
  (* two traces induced by inl transitions are finite
     because the underlying spinlock model is fairly terminating  *)
Admitted. 
  

Theorem comp_terminates
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [comp #()]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  set (Σ := gFunctors.app (heapΣ comp_model_impl) compΣ). 
  assert (heapGpreS Σ comp_model) as HPreG.
  { apply _. }

  unshelve eapply (@simulation_adequacy_terminate Σ _ comp_model _ NotStuck _ (None, None, Some 0) comp_free_roles_init) =>//.  
  - apply comp_model_term.  
  - eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (comp_model_finitary s1).
  - intros ?. iStartProof. iIntros "!> Hm HFR Hf !>".
    remember (lm_fl _ _) as fl. simpl.
    rewrite !set_map_empty !union_empty_l_L.  
    iApply (comp_spec _ ∅ True _ with "[] [Hm Hf HFR]"); eauto.
    { set_solver. }
    { iApply ActualOwnershipPartial.
      Unshelve. set_solver. } 
    iFrame. iSplitL "HFR".
    + iApply (partial_free_roles_are_Proper with "[HFR]"); [| iFrame].
      set_solver. 
    + (* TODO: generalize spec with arbitrary fuelmap *)
      admit. 
Admitted. 

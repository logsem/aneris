From iris.proofmode Require Import tactics.
Require Import stdpp.decidable.
From trillium.fairness Require Import fairness.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

Notation "'thread_id'" := (locale heap_lang).
Let heap_lang_extrace : Type := extrace heap_lang.

Section Spec.

  (* Context {Σ: gFunctors}.  *)
  Context `{!irisG heap_lang M Σ}. 

  Definition tm: val :=
    λ: <>,
      let: "n" := ref #1 in
      "n" <- #2.

  (* Definition wp_ph (e: expr) (τ: thread_id) (post: iProp Σ): iProp Σ. *)
  (* Admitted.  *)

  Definition thread_term (τ: thread_id): iProp Σ.
  Admitted.

  Lemma tm_term_spec (τ: thread_id):
    ⊢
      (* wp (tm #()) τ (thread_term τ). *)
      WP (tm #()) @ τ; ⊤ {{ _, thread_term τ }}. 
  Proof. Admitted. 

End Spec.


Section GeneralLemmas.

  (* typeclass stating that Σ stores model-related information. 
     TODO: should be completely arbitrary depending on the model?
     TODO: should the language be mentioned here?
     TODO: do we need to restrict Model to something more specific? *)
  Definition fairnessGpreS_ph (M: Model) (Σ: gFunctors): Prop.
  Admitted. 

  (* typeclass that allows program proofs.
     Contains fairnessGpreS_ph. 
     TODO: clarify where exactly it needed in wp_* lemmas
     TODO: clarify its relationship with invGS used to define WP.
   *)
  Definition heapGpreS_ph (Σ: gFunctors) (M: Model): Prop.
  Admitted. 
  
  (* a general version of simulation_adequacy_traces stating that 
     for every exec trace there exists a trace of model the WP is constructed against.
     TODO: this should hold for any model of WP, not only LM?  *)
Lemma simulation_adequacy_traces_general_ph:
∀ (Σ: gFunctors) {M : FairModel} (LM : LiveModel heap_lang M),
  heapGpreS Σ LM
  → ∀ (s : stuckness) (FR : gset (fmrole M)) (e1 : language.expr heap_lang) 
      (s1 : M) (extr : heap_lang_extrace),
      extrace_valid extr
      → (trfirst extr).1 = [e1]
        → rel_finitary (sim_rel LM)
          → live_roles M s1 ≠ ∅
            → (∀ heapGS0 : heapGS Σ LM,
                 ⊢ |={⊤}=>
                     frag_model_is s1 -∗
                     frag_free_roles_are (FR ∖ live_roles M s1) -∗
                     has_fuels 0 (gset_to_gmap (lm_fl LM s1) (live_roles M s1)) ={⊤}=∗
                     WP e1 @ s; 0; ⊤ {{ _, 0 ↦M ∅ }})
              → ∃ auxtr : auxtrace LM, exaux_traces_match extr auxtr

End GeneralLemmas.


Section Adequacy.



Theorem tm_terminates
  (extr: heap_lang_extrace)
  (Hvex: extrace_valid extr)
  (Hexfirst: (trfirst extr).1 = [tm (#())%V]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  (* assert (heapGpreS yesnoΣ the_model) as HPreG. *)
  (* { apply _. } *)
  eapply (simulation_adequacy_terminate_ftm yesnoΣ the_model NotStuck _ (N, true) ∅) =>//.
  - eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1).
  - destruct N; [lia|destruct N; set_solver].
  - intros ?. iStartProof. iIntros "!> Hm HFR Hf !>". simpl.
    iApply (start_spec _ _ 61 with "[Hm Hf HFR]"); eauto.
    + iSplitL "Hm"; eauto. do 2 (destruct N; first lia).
      assert (∅ ∖ {[ No; Y ]} = ∅) as -> by set_solver. iFrame. iSplit; last (iPureIntro; lia).
      assert ({[Y := 61%nat; No := 61%nat]} = gset_to_gmap 61 {[No;Y]}) as <-; last done.
      rewrite -leibniz_equiv_iff. intros ρ.
      destruct (gset_to_gmap 61 {[Y; No]} !! ρ) as [f|] eqn:Heq.
      * apply lookup_gset_to_gmap_Some in Heq as [Heq ->].
        destruct (decide (ρ = Y)) as [-> |].
        ** rewrite lookup_insert //. rewrite lookup_gset_to_gmap option_guard_True //. set_solver.
        ** rewrite lookup_insert_ne //. assert (ρ = No) as -> by set_solver.
           rewrite lookup_insert // lookup_gset_to_gmap option_guard_True //. set_solver.
      * apply lookup_gset_to_gmap_None in Heq. destruct ρ; set_solver.
Qed.

End Adequacy.

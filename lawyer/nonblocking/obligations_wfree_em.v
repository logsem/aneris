(* From iris.proofmode Require Import tactics. *)
(* From trillium.traces Require Import inftraces exec_traces trace_len.  *)
(* From trillium.program_logic Require Import execution_model weakestpre adequacy.  *)
(* From fairness Require Import fairness. *)
(* From lawyer.examples Require Import orders_lib. *)
(* From lawyer.obligations Require Import obligations_resources obligations_model obligations_em. *)


(* Section ObligationsWaitFreeEM. *)
(*   Context `{Countable (locale Λ)}. *)

(*   Context (ic: @trace_ctx Λ). (** location of the infinite call *) *)



(*   Definition obls_wfree_is_init_st (σ: cfg Λ) (δ: mstate OM): Prop. *)
(*   Admitted. *)
(*     (* obls_is_init_st σ δ /\ *) *)
    
(*   Lemma obls_wfree_resources_init Σ {PRE: ObligationsPreGS Σ}: *)
(*     ∀ s1 σ p (INIT: obls_is_init_st σ s1), *)
(*         ⊢ |==> ∃ eGS: ObligationsGS Σ, obls_init_resource s1 p ∗ obls_wfree_ti {tr[ σ ]} {tr[ s1 ]}. *)
(*   Proof using. *)
(*     clear H1 H0 H.  *)
(*     simpl. intros δ σ ? INIT. iStartProof. *)
(*     iMod (own_alloc (● (cps_repr $ ps_cps  δ) ⋅ ◯ _)) as (?) "[CPa CPf]". *)
(*     { by apply auth_both_valid_2. } *)
(*     iMod (own_alloc (● (sig_map_repr (ps_sigs δ)) ⋅ ◯ _)) as (?) "[SIGSa SIGSf]". *)
(*     { apply auth_both_valid_2; [| reflexivity]. *)
(*       rewrite /sig_map_repr. *)
(*       intros s. destruct lookup eqn:L; [| done]. *)
(*       apply lookup_fmap_Some in L.  *)
(*       destruct L as ([l b]&<-&?). *)
(*       done. } *)
(*     iMod (own_alloc (● (obls_map_repr $ ps_obls δ) ⋅ ◯ _)) as (?) "[OBLSa OBLSf]".  *)
(*     { apply auth_both_valid_discrete. split; [reflexivity| ]. *)
(*       intros τ. rewrite lookup_fmap.  *)
(*       by destruct lookup. } *)
(*     iMod (own_alloc (● (eps_repr $ ps_eps δ) ⋅ ◯ _)) as (?) "[EPSa EPSf]".  *)
(*     { by apply auth_both_valid_2. } *)

(*     iMod (ghost_map_alloc (wrap_phase <$> ps_phases δ)) as (?) "[PHa PHf]". *)
(*     iMod (own_alloc (●MN (ps_exc_bound δ) ⋅ mono_nat_lb _)) as (?) "[LBa LBf]". *)
(*     { apply mono_nat_both_valid. reflexivity. } *)
(*     iModIntro. iExists {| obls_pre := PRE; |}. *)
(*     rewrite big_sepM_fmap. iFrame. *)

(*     rewrite /cps_repr. iSplitL. *)
(*     { by iApply cps_mset. }  *)

(*     iPureIntro.  *)
(*     red in INIT. destruct INIT as (?&?). *)
(*     red. rewrite /threads_own_obls /dom_phases_obls. *)
(*     erewrite om_wf_dpo; eauto. *)
(*   Qed. *)
  
(*   Definition ObligationsEM: ExecutionModel Λ OM := *)
(*     {|  *)
(*       em_Σ := obls_Σ; *)
(*       em_valid_evolution_step := obls_valid_evolution_step; *)
(*       em_thread_post Σ `{!ObligationsGS Σ} := *)
(*         fun τ _ => (obls τ ∅)%I; *)
(*       em_initialization := obls_resources_init; *)
(*     |}. *)


(* End ObligationsWaitFreeEM. *)

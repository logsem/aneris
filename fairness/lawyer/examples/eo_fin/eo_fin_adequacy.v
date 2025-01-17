From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am multiset_utils.
From trillium.fairness.lawyer.examples.eo_fin Require Import eo_fin.
From trillium.fairness.lawyer.examples Require Import bounded_nat signal_map.


Section EOFinAdequacy.
  Context (B: nat).
  Let OP := EO_OP B.
  Existing Instance OP. 
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).
  Let OM := ObligationsModel. 
  Let M := AM2M ObligationsAM. 
  
  (* TODO: move *)
  Definition sig_mapΣ := #[GFunctor $ authUR (gmapUR nat (agreeR SignalId))].
  Global Instance subG_sig_mapΣ {Σ}: subG sig_mapΣ Σ → SigMapPreG Σ.
  Proof. solve_inG. Qed.

  Let eofinΣ: gFunctors := #[
      GFunctor (excl_authR natO); 
      sig_mapΣ;
      heapΣ EM
  ].

  Global Instance subG_eofinΣ {Σ}: subG eofinΣ Σ → EoFinPreG Σ.
  Proof. solve_inG. Qed.

  Definition obls_init_resource' `{!ObligationsGS Σ}
    (δ: mstate OM) (_: unit): iProp Σ :=
    ([∗ mset] '(π, d) ∈ (ps_cps δ), cp π d) ∗    
    own obls_sigs (◯ (sig_map_repr $ ps_sigs δ)) ∗
    own obls_obls (◯ (obls_map_repr $ ps_obls δ)) ∗
    own obls_eps (◯ (eps_repr $ ps_eps δ)) ∗
    ([∗ map] τ↦π ∈ ps_phases δ, th_phase_eq τ π) ∗
    exc_lb (ps_exc_bound δ)
  .
  Lemma obls_init_resource'_WIP `{!ObligationsGS Σ} δ p:
    obls_init_resource δ p = obls_init_resource' δ p.
  Proof using. Admitted.

  (* TODO: move *)
  Lemma cp_mul_alt `{oGS: !ObligationsGS Σ} π d n:
    cp_mul π d n (oGS := oGS) ⊣⊢ ([∗ mset] '(π, d) ∈ (n *: {[+ (π, d) +]}), cp π d (oGS := oGS)).
  Proof using.
    rewrite obligations_resources.cp_mul_unseal. rewrite /obligations_resources.cp_mul_def.
    iInduction n as [| n] "IH".
    { set_solver. }
    simpl. rewrite gmultiset_scalar_mul_S_l big_sepMS_disj_union.
    rewrite big_sepMS_singleton.
    iSplit; iIntros "[??]"; iFrame; by iApply "IH".
  Qed.

  (* TODO: move, replace original *)
    Lemma cp_mul_weaken `{oGS: ObligationsGS Σ} π1 π2 deg n1 n2
      (PH_LE: phase_le π1 π2)
      (LE: n2 <= n1):
      cp_mul π1 deg n1 (oGS := oGS) -∗ cp_mul π2 deg n2 (oGS := oGS).
    Proof using.
      iIntros "CPS".
      apply Nat.le_sum in LE as [? ->].
      iDestruct (cp_mul_split with "CPS") as "[CPS _]".
      rewrite obligations_resources.cp_mul_unseal.
      iInduction n2 as [| n] "IH".
      { set_solver. }
      simpl. iDestruct "CPS" as "[CP CPS]". iSplitL "CP".
      { by iApply cp_weaken. }
      by iApply "IH".
    Qed.

  Lemma eofin_terminates_impl
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([start #(0%nat) #B], Build_state ∅ ∅)):
    extrace_fairly_terminating extr. 
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := (2 * B + 5) *: {[+ d2 B +]} ⊎ 50 *: {[+ d0 B +]})
      (eb := 20); eauto.
    1-5: by apply _.
    1-2: by apply fin_wf.
    Unshelve. 2-6: by apply _.

    iIntros (?) "[HEAP INIT]".
    iApply (main_spec with "[-]").
    5: { simpl. iNext. iIntros (_) "X". iApply "X". }
    3: { simpl. iIntros (? _) "X". iApply "X". }
    { apply AMU_lift_top. }
    { intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top. }
    
    simpl. rewrite START.
    rewrite obls_init_resource'_WIP. 
    rewrite /obls_init_resource' /init_om_state. 
      
    rewrite init_phases_helper.
    rewrite locales_of_cfg_simpl. simpl.
    rewrite union_empty_r_L.
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    rewrite /cps_repr /sig_map_repr /eps_repr /obls_map_repr. 
    rewrite big_sepM_singleton. 
    rewrite fmap_empty.
    rewrite !gset_to_gmap_singleton. 
    rewrite map_fmap_singleton.      
    iFrame.
    rewrite mset_map_disj_union. rewrite big_sepMS_disj_union.
    rewrite !mset_map_mul !mset_map_singleton.
    rewrite -!cp_mul_alt. iDestruct "CPS" as "[CPS2 CPS0]".
    iSplitL "CPS2"; (iApply cp_mul_weaken; [..| by iFrame]; [apply phase_lt_fork | lia]).
  Qed. 

End EOFinAdequacy.

Theorem eofin_terminates (N: nat):
  forall extr,
    trfirst extr = ([start #(0%nat) #N], Build_state ∅ ∅) ->
    extrace_fairly_terminating extr.
Proof using.
  intros. eapply eofin_terminates_impl; eauto.  
Qed.

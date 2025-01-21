From iris.algebra Require Import auth gmap gset excl excl_auth mono_nat.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop. 
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am multiset_utils.
From trillium.fairness.lawyer.examples.ticketlock Require Import fair_lock ticketlock client.
From trillium.fairness.lawyer.examples Require Import bounded_nat signal_map.


Section Adequacy.
  (* Context (B: nat). *)
  (* Let OP := EO_OP B. *)
  (* Existing Instance OP.  *)
  (* Let ASEM := ObligationsASEM. *)
  (* Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)). *)
  (* Let OM := ObligationsModel.  *)
  (* Let M := AM2M ObligationsAM.  *)
  

  (* TODO: move *)
  Definition sig_mapΣ := #[GFunctor $ authUR (gmapUR nat (agreeR SignalId))].
  Global Instance subG_sig_mapΣ {Σ}: subG sig_mapΣ Σ → SigMapPreG Σ.
  Proof. solve_inG. Qed.

  (* TODO: move, use in eo_fin adequacy *)
  Definition bn_ith N (i: nat): bounded_nat (S N) :=
    match (le_lt_dec (S N) i) with
    | left GE => ith_bn (S N) 0 ltac:(lia)                                      
    | right LT => ith_bn (S N) i LT
    end.

  Lemma bn_ith_simpl N i (DOM: i < S N):
    bn_ith N i = ith_bn (S N) i DOM.
  Proof.      
    rewrite /bn_ith. destruct le_lt_dec; [lia| ].
    f_equal. eapply Nat.lt_pi.
  Qed.

  Definition ClosedDegree := bounded_nat 6.
  Definition CD (i: nat): ClosedDegree := bn_ith 5 i.
  Let d__r := CD 5.
  Let d__m := CD 4.
  Let d__e := CD 3.
  Let d__h := CD 2.
  Let d__l := CD 1.
  Let d__w := CD 0.
  Let d0 := CD 0.

  Definition ClosedLevel := bounded_nat 3.
  Definition CL (i: nat): ClosedLevel := bn_ith 2 i.
  Let l__f := CL 2.
  Let l__acq := CL 1.
  Let l0 := CL 0.

  (* TODO: make the lower bounds separate definitions in ticketlock module *)
  Definition ClosedLim := max_list [2 + tl_exc; 2 * c__cl + 3 + tl_exc].

  Instance ClosedObligationsPre: ObligationsParamsPre ClosedDegree ClosedLevel ClosedLim.
    esplit; try by apply _.
    all: apply nat_bounded_PO. 
  Defined.

  Definition TLΣ := #[
    GFunctor $ authUR (gmapUR nat (exclR $ tau_codom_gn (OPRE := ClosedObligationsPre)));
    savedPredΣ (val heap_lang);
    savedPredΣ (option nat);
    GFunctor $ authUR (gset_disjUR natO);
    GFunctor $ excl_authUR boolO;
    GFunctor $ mono_natUR;
    GFunctor $ exclR unitO
  ].
  Global Instance subG_TLΣ {Σ}: subG TLΣ Σ → TicketlockPreG Σ (OPRE := ClosedObligationsPre).
  Proof. solve_inG. Qed.

  Definition ClientΣ := #[
    GFunctor $ excl_authUR (optionUR SignalId);
    GFunctor $ @one_shotR unitO;
    sig_mapΣ
  ].

  Global Instance subG_clientΣ {Σ}: subG ClientΣ Σ → ClientPreG Σ.
  Proof. solve_inG. Qed.

  Definition ClosedOP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance ClosedOP. 
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).
  Let OM := ObligationsModel. 
  Let M := AM2M ObligationsAM. 

  Definition ClosedΣ := #[ TLΣ; ClientΣ; heapΣ EM].

  Program Definition TLPreInstance := TLPre d__l d__h d__e d__m _ _ _ l__acq (OPRE := ClosedObligationsPre).
  Next Obligation. apply ith_bn_lt. lia. Qed. 
  Next Obligation. apply ith_bn_lt. lia. Qed. 
  Next Obligation. apply ith_bn_lt. lia. Qed.

  Lemma closed_program_terminates_impl
    (prog := client_prog (FLP := TLPreInstance))
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([prog #()], Build_state ∅ ∅)):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS ClosedΣ EM) as HPreG.
    { apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := 4 *: {[+ d__r +]})
      (eb := 70); eauto.
    1-5: by apply _.
    1-2: by apply fin_wf.

    iIntros (?) "[HEAP INIT]".

    eset (tfl := TL_FL). specialize (tfl d__w d__l d__h d__e d__m).
    specialize tfl with (lvl_acq := l__acq) (hGS := HEAP) (oGS := (@heap_fairnessGS _ _ _ HEAP)).

    pose proof @client_spec as SPEC. specialize SPEC with (OPRE := ClosedObligationsPre) (hGS := HEAP) (oGS := (@heap_fairnessGS _ _ _ HEAP)).
    specialize SPEC with (l__o := l0) (l__f := l__f) (l__fl := l__acq) (d0 := d0) (d__r := d__r).

    iApply (SPEC with "[-]").
    { apply tfl. 
      - apply ith_bn_lt. lia.
      - apply AMU_lift_top.
      - rewrite /ClosedLim. etrans.
        2: { apply max_list_elem_of_le, elem_of_list_here. }
        lia. }
    1, 2: simpl; rewrite /lvls_acq; intros ? ->%elem_of_singleton; apply ith_bn_lt; lia.
    { apply ith_bn_lt; lia. }
    { simpl. rewrite /lvls_acq. by apply elem_of_singleton. }
    { apply AMU_lift_top. }
    1, 2: apply ith_bn_lt; lia.
    1, 2, 3: rewrite /ClosedLim; simpl; rewrite /tl_exc; lia. 
    { intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top. }
    { simpl. iIntros (? _) "X". iApply "X". }
    { simpl. by apply _. }
    2: { simpl. iNext. iIntros (_) "X". iApply "X". }

    clear SPEC tfl.     
    rewrite START. simpl.
    rewrite /obls_init_resource /init_om_state.      
    rewrite init_phases_helper.
    rewrite locales_of_cfg_simpl. simpl.
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    rewrite union_empty_r_L !gset_to_gmap_singleton.
    rewrite big_sepM_singleton. iFrame.  
    rewrite /cps_repr /sig_map_repr /eps_repr /obls_map_repr.
    rewrite !fmap_empty map_fmap_singleton.      
    iFrame.
    rewrite !mset_map_mul !mset_map_singleton.
    rewrite -!(cp_mul_alt (oGS := (@heap_fairnessGS _ _ _ HEAP))).
    iApply cp_mul_weaken; [..| by iFrame]; apply phase_lt_fork || lia. 
  Qed.

End Adequacy.


Theorem closed_program_terminates:
  forall extr,
    trfirst extr = ([client_prog (OPRE := ClosedObligationsPre) (FLP := TLPreInstance) #()], Build_state ∅ ∅) ->
    extrace_fairly_terminating extr.
Proof using.
  intros. eapply closed_program_terminates_impl; eauto.  
Qed.

Print Assumptions closed_program_terminates.

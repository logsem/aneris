From iris.algebra Require Import auth gmap gset excl excl_auth mono_nat.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop. 
From fairness Require Import utils.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am env_helpers.
From lawyer.examples.ticketlock Require Import fair_lock ticketlock client releasing_lock ticketlock_releasing.
From lawyer.examples Require Import orders_lib signal_map.


Section Adequacy.  

  Definition ClosedDegree := bounded_nat 7.
  Definition CD (i: nat): ClosedDegree := bn_ith 6 i.
  Let d__r := CD 6.
  Let d__m' := CD 5.
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

  Definition ClosedLim := max_list [tl_c__cr; tl_fl_B c__cl; MAX_EXC + 2].

  Instance ClosedObligationsPre: ObligationsParamsPre ClosedDegree ClosedLevel ClosedLim.
    esplit; try by apply _.
    all: apply nat_bounded_PO. 
  Defined.

  Instance Closed_OP_HL: OP_HL ClosedDegree ClosedLevel ClosedLim.
  esplit; by apply _.
  Defined. 
  

  Definition TLΣ := #[
    GFunctor $ authUR (gmapUR nat (exclR $ tau_codom_gn));
    savedPredΣ (val heap_lang);
    savedPredΣ (option nat);
    GFunctor $ authUR (gset_disjUR natO);
    GFunctor $ excl_authUR boolO;
    GFunctor $ mono_natUR;
    GFunctor $ exclR unitO
  ].
  Global Instance subG_TLΣ {Σ}: subG TLΣ Σ → TicketlockPreG Σ.
  Proof. solve_inG. Qed.

  Definition ClientΣ := #[
    GFunctor $ excl_authUR (optionUR SignalId);
    sig_mapΣ
  ].

  Global Instance subG_clientΣ {Σ}: subG ClientΣ Σ → ClientPreG Σ.
  Proof.
    (* solve_inG. *)
  Qed.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).

  Program Definition TLPreInstance' :=
    TLPreInstance l__acq d__l d__h d__e d__m _ _ _ (OP := Closed_OP_HL) (EM := EM).
  Solve All Obligations with apply ith_bn_lt; lia.
  Fail Next Obligation.

  Program Definition TLInstance' :=
    TL_FL d__w d__l d__h d__e d__m _ _ _ _ _ l__acq (OP := Closed_OP_HL) (EM := EM).
  Solve Obligations with apply ith_bn_lt; lia.
  Next Obligation.
    rewrite /ClosedLim. cbv. lia.
  Qed.
  Fail Next Obligation.

  Program Definition RFLInstance' :=
    RFL_FL_TL' {[ l__acq ]} l0 _ l__acq _
      d__w d__l d__h d__e d__m d__m' _ _ _ _ _
      _ (OP := Closed_OP_HL) (EM := EM).
  Next Obligation.
    simpl. intros ?. rewrite /lvls_acq elem_of_singleton. intros ->.
    apply ith_bn_lt. lia.
  Qed.
  Next Obligation.
    set_solver.
  Qed.
  Solve Obligations with (simpl; apply ith_bn_lt; lia).
  Next Obligation.
    rewrite /ClosedLim /tl_exc. simpl. lia.
  Qed.
  Fail Next Obligation.

  Definition RFLΣ := #[GFunctor $ excl_authUR (optionUR SignalId); sig_mapΣ; TLΣ].
  Global Instance subG_RFLΣ {Σ}: subG RFLΣ Σ → RFL_FL_preG Σ (FLP := TLPreInstance').
  Proof. intros. esplit; solve_inG. Qed. 

  Definition ClosedΣ := #[ ClientΣ;
                           heapΣ EM;
                           RFLΣ
                          ].

  Instance Closed_OM_HL_Env
    (HEAP: heapGS ClosedΣ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ, obls τ ∅))):
    OM_HL_Env Closed_OP_HL EM ClosedΣ.
  Proof.
    unshelve esplit; try by apply _.
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top.
    - intros. rewrite -nclose_nroot. apply AMU_lift_top.
  Defined.

  Lemma closed_program_terminates_impl
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([client_prog RFLInstance' #()], Build_state ∅ ∅)):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS ClosedΣ EM) as HPreG.
    { apply subG_heapPreG. apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := 4 *: {[+ d__r +]})
      (eb := 70); eauto.
    1-5: by apply _.
    1-2: by apply fin_wf.

    iIntros (?) "[HEAP INIT]".

    simpl in *. 

    pose proof @client_spec as SPEC.
    specialize SPEC with (OP := Closed_OP_HL) (RFL := RFLInstance') (OHE := Closed_OM_HL_Env HEAP).
    specialize SPEC with (l__f := l__f) (d0 := d0) (d__r := d__r).
    simpl in *.

    iApply (SPEC with "[-]").
    { simpl. intros ?. rewrite /rfl_fl_lvls. simpl. rewrite /lvls_acq.
      rewrite elem_of_union !elem_of_singleton.
      intros [-> | ->]; apply ith_bn_lt; lia. }
    1, 2: apply ith_bn_lt; lia. 
    { cbv; lia. }
    { simpl. by iIntros (? _) "X". }
    { (* TODO: why solve_inG doesn't solve it? *)
      intros. split; try solve_inG || apply _.
      simpl. apply _. }
    2: { by iIntros "!> % ?". }

    clear SPEC.
    rewrite START. simpl.
    iDestruct (closed_pre_helper with "[$]") as "(?&?&?&?)".
    iFrame. 
    iApply cp_mul_weaken; [..| by iFrame]; [reflexivity | lia]. 
  Qed.

End Adequacy.


Theorem closed_program_terminates:
  forall extr,
    trfirst extr = ([client_prog RFLInstance' #()], Build_state ∅ ∅) ->
    extrace_fairly_terminating extr.
Proof using.
  intros. eapply closed_program_terminates_impl; eauto.  
Qed.

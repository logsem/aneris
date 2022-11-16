From stdpp Require Import base fin_maps gmap.
From iris.base_logic.lib Require Export invariants.
From aneris.prelude Require Import gset_map.
From aneris.lib Require Export dfrac_oneshot.
From aneris.aneris_lang Require Export tactics proofmode.
From aneris.aneris_lang.lib Require Export
     pers_socket_proto set_proof nodup_proof.
From aneris.examples.transaction_commit Require Export
     two_phase_code tc_model gen_mono_heap.

Definition TC_model (RMs : gset socket_address) : resources.Model :=
  model _ (TCNext RMs) (TCInit RMs).
Notation TCState := (@TCState socket_address).

(** The resource managers node-local transition relation is monotone *)
Section RM_state_relation.

  Definition rm_stateO := leibnizO rm_state.

  Inductive rm_step : relation rm_stateO :=
  | step_prepare         : rm_step WORKING PREPARED
  | step_commit          : rm_step PREPARED COMMITTED
  | step_working_abort   : rm_step WORKING ABORTED
  | step_prepared_abort  : rm_step PREPARED ABORTED.

  Definition rm_step_rtc := rtc rm_step.

  Global Instance: ProperPreOrder rm_step_rtc.
  Proof. split; apply _. Qed.

  Global Instance: AntiSymm (≡) rm_step_rtc.
  Proof.
    rewrite /AntiSymm.
    destruct 1 as [|? ? z Hstep1 ?]; [done|].
    destruct 1 as [|u ? ? Hstep2 ?]; [done|].
    destruct z, u; inversion Hstep1; inversion Hstep2; simplify_eq; try done;
      match goal with
      | [ H: rtc rm_step COMMITTED ?x |- _ ] => inversion H; try done
      | [ H: rtc rm_step ABORTED ?x |- _ ] => inversion H; try done
      end;
      match goal with
      | [ H: rm_step ?d ?x |- _ ] => inversion H; simplify_eq; try done
      end.
  Qed.

  Hint Constructors rm_step : core.
  Hint Constructors rtc : core.

  Lemma rm_step_rtc_not_committed s :
    s ≠ COMMITTED →
    ¬ (rm_step_rtc COMMITTED s).
  Proof. inversion 2 as [|??? []]; simplify_eq. Qed.

  Lemma rm_step_rtc_not_aborted s :
    s ≠ ABORTED →
    ¬ (rm_step_rtc ABORTED s).
  Proof. inversion 2 as [|??? []]; simplify_eq. Qed.

  Lemma rm_step_rtc_not_prepared_working :
    ¬ (rm_step_rtc PREPARED WORKING).
  Proof.
    inversion 1 as [|??? He Hcon]; simplify_eq.
    destruct y; inversion He; simplify_eq.
    - by eapply (rm_step_rtc_not_committed WORKING).
    - by eapply (rm_step_rtc_not_aborted WORKING).
  Qed.

  Lemma rm_step_rtc_working_any s : rm_step_rtc WORKING s.
  Proof. rewrite /rm_step_rtc. destruct s; eauto. Qed.

  Lemma rm_step_rtc_aborted s :
    rm_step_rtc ABORTED s → s = ABORTED.
  Proof. inversion 1 as [|??? Hstp]; [done|]. inversion Hstp. Qed.

  Lemma rm_step_rtc_committed s :
    rm_step_rtc COMMITTED s → s = COMMITTED.
  Proof. inversion 1 as [|??? Hstp]; [done|]. inversion Hstp. Qed.

End RM_state_relation.

Class tcPreG Σ := {
  tc_gen_mono_heap_inPreG :>
    gen_mono_heapPreG socket_address rm_stateO rm_step_rtc Σ;
  tc_oneshot_inPreG :> inG Σ (dfrac_oneshotR unitO)
}.
Definition tcΣ : gFunctors :=
  #[dfrac_oneshotΣ unitO; gen_mono_heapGΣ _ rm_step_rtc].
Instance subG_tcΣ {Σ} : subG tcΣ Σ → tcPreG Σ.
Proof. solve_inG. Qed.

Class tcG Σ := MkTcG {
  tc_oneshot_inG :> inG Σ (dfrac_oneshotR unitO);
  tc_gen_mono_heap_inG :>
    gen_mono_heapG socket_address rm_stateO rm_step_rtc Σ;
  tc_oneshot_gname : gname;
}.

Class network_topo := {
  (* resource managers *)
  RMs : gset socket_address;
  (* transaction manager *)
  tm : socket_address;
  RMs_notempty : RMs ≠ ∅;
}.

Section tpc_prelude.
  Context `{!network_topo}.
  Context `{!anerisG (TC_model RMs) Σ, !tcG Σ}.

  (* a fraction for every RM and the TM *)
  Definition pending := pending tc_oneshot_gname (/ nat_to_Qp (size RMs + 1)).
  Definition pending_discarded := pending_discarded tc_oneshot_gname.
  Definition shot := shot tc_oneshot_gname ().

  Definition state_to_msg (rm : socket_address) (st : rm_state) :=
    let msg s := mkMessage rm tm s in
    match st with
    | WORKING   => None
    | PREPARED  => Some (msg "PREPARED")
    | COMMITTED => Some (msg "COMMITTED")
    | ABORTED   => Some (msg "ABORTED")
    end.

  Instance state_to_msg_inj rm : Inj (=) (=) (state_to_msg rm).
  Proof. by intros [] []; simplify_eq. Qed.

  Definition state_message_coh rm st (T : gset message) :=
    if state_to_msg rm st is Some msg then msg ∈ T else True.

  (* The sent messages [T] are consistent with [rm] being in (at least) state [st] *)
  Definition messages_model_agree rm st (T : gset message):=
    state_message_coh rm st T ∧
    ∀ st', state_message_coh rm st' T → rm_step_rtc st' st.

  Definition rm_si : socket_interp Σ  :=
    (λ m,
      (⌜m_body m = "PREPARE"⌝) ∨
      (⌜m_body m = "COMMIT"⌝ ∗ shot ∗ [∗ set] rm ∈ RMs, rm ↦◯ PREPARED) ∨
      (⌜m_body m = "ABORT"⌝  ∗ pending_discarded))%I.

  Definition tm_si : socket_interp Σ  :=
    (λ m, ⌜m_sender m ∈ RMs⌝ ∗
     ((⌜m_body m = "PREPARED"⌝  ∗ m_sender m ↦◯ PREPARED  ∗ pending) ∨
      (⌜m_body m = "COMMITTED"⌝ ∗ m_sender m ↦◯ COMMITTED ∗ shot) ∨
      (⌜m_body m = "ABORTED"⌝   ∗ m_sender m ↦◯ ABORTED   ∗ pending_discarded)))%I.

  Definition state_tok_coh st : iProp Σ :=
    match st with
    | COMMITTED => shot
    | ABORTED => pending_discarded
    | _ => True
    end.

  Global Instance state_tok_coh_timesless st : Timeless (state_tok_coh st).
  Proof. destruct st; apply _. Qed.

  Definition rm_inv (mdl : TCState) : iProp Σ :=
    ([∗ set] rm ∈ RMs, ∃ (R T : message_soup) (st : rm_state),
        (* the model is tracked node-locally by [rm ↦●{1/2} st] *)
        ⌜mdl !! rm = Some st⌝ ∗ rm ↦●{1/2} st ∗
        (* we globally encode the protocol using the ghost resources  *)
        state_tok_coh st ∗
        (* the model is linked to the program state by sent messages *)
        rm @ rm_si ⤳# (R, T) ∗ ⌜messages_model_agree rm st T⌝)%I.
  Definition tc_inv : iProp Σ :=
    ∃ mdl, frag_st mdl ∗ rm_inv mdl.
  Definition tcN := nroot.@"tc".

  Lemma tc_inv_alloc E :
    frag_st (TCInit RMs) ∗
    ([∗ set] rm ∈ RMs, rm ↦●{1/2} WORKING) ∗
    ([∗ set] rm ∈ RMs, rm ⤳ (∅, ∅))
    ⊢ |={E}=> inv tcN tc_inv.
  Proof.
    iIntros "(Hfrag & Hwork & Hrms)".
    iApply inv_alloc.
    iModIntro. iExists _. iFrame. rewrite /rm_inv.
    iCombine "Hrms Hwork" as "Hrms". rewrite -big_sepS_sep.
    iApply (big_sepS_impl with "Hrms").
    iIntros "!#" (rm ?) "[Hrm Hw]".
    iExists _, _, _. iFrame.
    iSplit.
    { rewrite lookup_gset_to_gmap_Some //. }
    iSplit; [done|].
    iSplitL.
    { by iApply (mapsto_messages_pers_alloc with "Hrm"). }
    iSplit; [done|].
    by iIntros ([]).
  Qed.

  Lemma messages_model_agree_send st st' m rm T :
    rm_step st st' →
    state_to_msg rm st' = Some m →
    messages_model_agree rm st T →
    messages_model_agree rm st' ({[m]} ∪ T).
  Proof.
    intros Hstep Hm [Hcoh HT]. split.
    - rewrite /state_message_coh. case_match; [|done].
      simplify_eq. set_solver.
    - rewrite /state_message_coh.
      intros st'' Hcoh'; case_match eqn : Heqo; last first.
      { destruct st''; [|done..]. apply rm_step_rtc_working_any. }
      apply elem_of_union in Hcoh' as [?%elem_of_singleton | ?]; simplify_eq.
      { rewrite -Hm in Heqo. simplify_eq. done. }
      specialize (HT st'').
      eapply rtc_r; [eapply HT|done].
      rewrite /state_message_coh.
      by case_match; simplify_eq.
  Qed.

  Lemma rm_inv_mdl_Exact rm st mdl :
    rm ∈ RMs →
    rm ↦●{1/2} st -∗
    rm_inv mdl -∗
    ⌜mdl !! rm = Some st⌝.
  Proof.
    iIntros (?) "HE Hinv".
    rewrite /rm_inv (big_sepS_elem_of _ _ rm) //.
    iDestruct "Hinv" as (R T st') "(% & HE' & _)".
    by iDestruct (mono_mapsto_agree with "HE HE'") as %<-.
  Qed.

  Lemma rm_inv_pending_notcommitted mdl :
    rm_inv mdl -∗
    pending -∗
    ⌜notCommitted RMs mdl⌝.
  Proof.
    iIntros "Hinv Hpend" (rm ??).
    rewrite /rm_inv (big_sepS_elem_of _ _ rm) //.
    iDestruct "Hinv" as (?? st) "(% & HE & Hshot & _)".
    simplify_map_eq.
    iApply (pending_shot with "Hpend Hshot").
  Qed.

  Lemma rm_inv_pending_discarded_notcommitted mdl :
    rm_inv mdl -∗
    pending_discarded -∗
    ⌜notCommitted RMs mdl⌝.
  Proof.
    iIntros "Hinv Hpend" (rm ??).
    rewrite /rm_inv (big_sepS_elem_of _ _ rm) //.
    iDestruct "Hinv" as (?? st) "(% & HE & Hshot & _)".
    simplify_map_eq.
    iApply (pending_discarded_shot with "Hpend Hshot").
  Qed.

  Lemma rm_inv_cancommit mdl :
    rm_inv mdl -∗
    ([∗ set] rm ∈ RMs, rm ↦◯ PREPARED) -∗
    shot -∗
    ⌜canCommit RMs mdl⌝.
  Proof.
    iIntros "Hinv Hal Hshot" (rm ?).
    rewrite /rm_inv !(big_sepS_elem_of _ _ rm) //.
    iDestruct "Hinv" as (?? st) "(% & HE & Hpend & _)".
    iDestruct (mono_mapsto_related with "HE Hal") as %Hrel.
    simplify_map_eq.
    destruct st; auto; simpl.
    - by apply rm_step_rtc_not_prepared_working in Hrel.
    - by iDestruct (pending_discarded_shot with "Hpend Hshot") as %?.
  Qed.

  (* TODO: upstream? *)
  Lemma big_sepS_set_seq `{Countable A} n (P : iProp Σ) (X : gset A) :
    ([∗ set] _ ∈ X, P) ⊢ [∗ set] _ ∈ set_seq n (size X), P.
  Proof.
    revert n.
    induction X using set_ind_L; intros n.
    { rewrite size_empty /=. auto. }
    rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
    iIntros "[HP HX]".
    rewrite size_union ?size_singleton; [|set_solver].
    rewrite set_seq_add_L.
    rewrite big_sepS_union /=; [|set_solver by lia].
    rewrite union_empty_r_L big_sepS_singleton.
    iFrame. by iApply IHX.
  Qed.

  Lemma tm_shot_prepared :
    pending -∗ ([∗ set] _ ∈ RMs, pending) ==∗ shot.
  Proof.
    iIntros "Hpend Hpends".
    iPoseProof (big_sepS_set_seq 0 with "Hpends") as "Hpends".
    iCombine "Hpend Hpends" as "Hpends".
    rewrite -(big_sepS_insert _ _ (size RMs)); [|set_solver by lia].
    assert (∀ n, {[n]} ∪ set_seq 0 n = set_seq 0 (n + 1))
      as -> by set_solver by lia.
    rewrite -pending_split_N; [|lia].
    iMod (pending_update_shot with "Hpends") as "#Hshot".
    by iFrame.
  Qed.

  Lemma tm_rm_committed d (ms : message_soup) :
    shot -∗
    ([∗ map] rm↦b ∈ d, ∃ m, ⌜m ∈ ms⌝ ∗ ⌜m_destination m = tm⌝ ∗
                            ⌜m_sender m = rm⌝ ∗ ⌜m_body m = b⌝ ∗ tm_si m) -∗
    [∗ map] rm↦b ∈ d, ⌜b = "COMMITTED"⌝ ∗ rm ↦◯ (COMMITTED : rm_stateO).
  Proof.
    iIntros "#Hshot HRMs".
    iApply (big_sepM_impl with "HRMs").
    iIntros "!#" (rm Hi ?).
    iDestruct 1 as (m) "(% & % & <- & Hm)".
    rewrite /tm_si.
    iDestruct "Hm" as "(% & % & [(_ & _ & Hpend) | [(% & Hal & _) | (_ & _ & Hdisc)]])".
    { by iDestruct (pending_shot with "Hpend Hshot") as %?. }
    { simplify_eq. by iFrame. }
    { by iDestruct (pending_discarded_shot with "Hdisc Hshot") as %?. }
  Qed.

End tpc_prelude.

From aneris.aneris_lang Require Import lang inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.


Global Instance int_time : DB_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.

Instance: Inhabited (@we int_time) := populate (Build_we "" #() inhabitant).

Global Program Instance Inject_write_event : Inject we val :=
  {| inject a := $(a.(we_key), a.(we_val), a.(we_time))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ht]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Z_of_nat_inj in Ht; subst.
Qed.

Definition write_event := @we int_time.
Definition write_eventO := leibnizO write_event.
Definition wrlog := list write_eventO.


(* -------------------------------------------------------------------------- *)
(** The state validity defines coherence of the log and the memory model. *)

Section ValidStates.
  Context `{!DB_params}.

  (** Global Validity. *)
  Definition mem_dom (M : gmap Key (option write_event)) := DB_keys = dom M.

  Definition mem_we_key (M : gmap Key (option write_event)) :=
    ∀ k we, M !! k = Some (Some we) → we.(we_key) = k.

  Definition mem_log_coh (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ k, k ∈ dom M → M !! k = Some (at_key k L).

  Definition in_log_mem_some_coh (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ k we, at_key k L = Some we → M !! k = Some (Some we).

 Definition mem_serializable_vals (M : gmap Key (option write_event)) :=
    ∀ k we, M !! k = Some (Some we) → Serializable DB_serialization we.(we_val).

  Definition allocated_in_mem (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ l k wel, l ≤ₚ L → at_key k l = Some wel →
               ∃ weL, M !! k = Some (Some weL) ∧ wel ≤ₜ weL.

  (* why are scopes screwed up here!? *)
  Definition log_events (L : wrlog) :=
    ∀ (i : nat), (i < List.length L)%nat →
         ∃ we, L !! i = Some we ∧ i = we.(we_time) ∧ we.(we_key) ∈ DB_keys ∧
                 Serializable DB_serialization we.(we_val).

  Record valid_state (L : wrlog) (M : gmap Key (option write_event)) : Prop :=
    {
      DB_GSTV_mem_dom : mem_dom M;
      DB_GSTV_mem_we_key : mem_we_key M;
      DB_GSTV_mem_log_coh : mem_log_coh L M;
      DB_GSTV_mem_in_log_mem_some_coh : in_log_mem_some_coh L M;
      DB_GSTV_mem_serializable_vals : mem_serializable_vals M;
      DB_GSTV_mem_allocated_in_mem : allocated_in_mem L M;
      DB_GSTV_log_events : log_events L;
    }.

  Lemma valid_state_empty :
    valid_state [] (gset_to_gmap (@None write_event) DB_keys).
  Proof.
    split; rewrite /mem_dom /mem_we_key /mem_log_coh /in_log_mem_some_coh
                   /mem_serializable_vals /allocated_in_mem /log_events.
    - by rewrite dom_gset_to_gmap.
    - intros ? ? Habs. apply lookup_gset_to_gmap_Some in Habs. naive_solver.
    - intros k Hy2. apply lookup_gset_to_gmap_Some. rewrite dom_gset_to_gmap in Hy2. naive_solver.
    - intros k we He. naive_solver.
    - intros k we Hnone. apply lookup_gset_to_gmap_Some in Hnone. naive_solver.
    - intros l k wel Hpre Hsm. destruct Hpre as (h2 & Hpre).
      symmetry in Hpre. apply app_eq_nil in Hpre. naive_solver.
    - intros i Hin. rewrite nil_length in Hin. by lia.
  Qed.

  Lemma log_events_serializable L M :
    valid_state L M →
    ∀ (we : write_event),
    we ∈ L →
    Serializable
     (prod_serialization
        (prod_serialization string_serialization DB_serialization)
        int_serialization) ($ we).
  Proof.
    intros Hvs we Hwe.
    destruct we as [k v t].
    apply (_ : _ → _ → Serializable (prod_serialization _ _) (_, _)); last apply _.
    apply (_ : _ → _ → Serializable (prod_serialization _ _) (_, _)); first apply _.
    apply elem_of_list_lookup_1 in Hwe as [i Hiwe].
    destruct (DB_GSTV_log_events _ _ Hvs i) as (?&Hi&?&?&?);
      first by eapply lookup_lt_is_Some_1; eauto.
    rewrite Hi in Hiwe; simplify_eq; done.
  Qed.


  (* TODO: MOVE *)
  Lemma prefix_of_snoc {A} x (l1 l2 : list A) : l1 ≤ₚ (l2 ++ [x]) → l1 = l2 ++ [x] ∨ l1 ≤ₚ l2.
  Proof.
    intros [k Hk]. destruct k as [|y k _] using rev_ind .
    - rewrite app_nil_r in Hk; by left.
    - rewrite assoc in Hk. apply app_inj_2 in Hk as [? ?]; last done.
      right; eexists; done.
  Qed.

  (* TODO: MOVE *)
  Lemma at_key_elem_of k l we : at_key k l = Some we → we ∈ l.
  Proof. intros ?; eapply elem_of_list_filter; apply last_Some_elem_of; done. Qed.

(* TODO: MOVE *) (* again scope is screwed up! *)
  Lemma lt_TM_lt we we' : (we_time we < we_time we')%nat → we ≤ₜ we'.
  Proof. rewrite /TM_lt /=; by left. Qed.

  Lemma log_events_state_update (lM : wrlog) wev :
    wev.(we_key) ∈ DB_keys →
    wev.(we_time) = length lM →
    Serializable DB_serialization wev.(we_val) →
    log_events lM ->
    log_events (lM ++ [wev]).
  Proof.
    intros ??? HLE i. rewrite app_length /=. intros Hi.
    destruct (decide (i = length lM)) as [->|].
    + rewrite lookup_app_r; last done.
      rewrite Nat.sub_diag /=.
      eexists _; done.
    + destruct (HLE i) as (?&Hi'&?&?&?); first lia.
      eexists; split; last done.
      rewrite lookup_app_l; first done.
      apply lookup_lt_is_Some_1; eauto.
  Qed.

  Lemma valid_state_update (lM : wrlog) (kvsMG : gmap Key (option write_event)) wev :
    wev.(we_key) ∈ DB_keys →
    wev.(we_time) = length lM →
    Serializable DB_serialization wev.(we_val) →
    valid_state lM kvsMG ->
    valid_state (lM ++ [wev]) (<[wev.(we_key) := Some wev]> kvsMG).
  Proof.
    intros Hwevk Hwevt Hwevser Hvs.
    split.
    - rewrite /mem_dom dom_insert_L subseteq_union_1_L; first apply Hvs.
      erewrite <- DB_GSTV_mem_dom; last done.
      set_solver.
    - intros k we.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite lookup_insert; intros ?; simplify_eq; done. }
      rewrite lookup_insert_ne; last done.
      apply Hvs; done.
    - intros k. rewrite dom_insert elem_of_union elem_of_singleton. intros Hk.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite lookup_insert at_key_snoc_some; done. }
      destruct Hk as [->|Hk]; first done.
      rewrite lookup_insert_ne; last done.
      rewrite at_key_snoc_none; last done.
      apply Hvs; done.
    - intros k we.
      destruct (decide (k = we_key wev)) as [->|].
      + rewrite lookup_insert at_key_snoc_some; last done; intros ?; simplify_eq; done.
      + rewrite lookup_insert_ne; last done.
        rewrite at_key_snoc_none; last done.
        apply Hvs.
    - intros k we.
      destruct (decide (k = we_key wev)) as [->|].
      + rewrite lookup_insert; intros ?; simplify_eq; done.
      + rewrite lookup_insert_ne; last done. apply Hvs.
    - intros l k wel Hl Hklwel.
      destruct (decide (k = we_key wev)) as [->|].
      + rewrite lookup_insert. eexists; split; first done.
        apply prefix_of_snoc in Hl as [->|Hl].
        { rewrite at_key_snoc_some in Hklwel; last done; simplify_eq.
          by right. (* this is weird; need to prove the Reflexive instance for ≤ₜ *) }
        assert (∃ i, lM !! i = Some wel) as [i Hi].
        { apply elem_of_list_lookup.
          eapply elem_of_prefix; last done.
          eapply at_key_elem_of; done. }
        apply lt_TM_lt.
        destruct (DB_GSTV_log_events _ _ Hvs i) as (?&Hi'&?&?&?);
          first by apply lookup_lt_is_Some_1; eauto.
        rewrite /TM_lt /=.
        rewrite Hi in Hi'; simplify_eq.
        rewrite Hwevt.
        apply lookup_lt_is_Some_1; eauto.
      + rewrite lookup_insert_ne; last done.
        apply prefix_of_snoc in Hl as [->|Hl].
        { rewrite at_key_snoc_none in Hklwel; last done; simplify_eq.
          eapply Hvs; done. }
        eapply Hvs; done.
    - apply log_events_state_update; [done|done|done|apply Hvs].
  Qed.

  Lemma log_events_no_dup lM : log_events lM → NoDup lM.
  Proof.
    intros HLE.
    apply (NoDup_fmap_1 we_time).
    assert (we_time <$> lM = seq 0 (length lM)) as ->; last apply NoDup_seq.
    apply list_eq.
    intros i.
    destruct (decide (i < length lM)%nat); last first.
    { rewrite lookup_seq_ge; last lia.
      rewrite list_lookup_fmap lookup_ge_None_2; first done. by apply Nat.nlt_ge. }
    rewrite lookup_seq_lt /=; last done.
    destruct (HLE i) as (?&Hi&Hit&?&?); first done.
    rewrite list_lookup_fmap Hi /= -Hit //.
  Qed.

  Lemma valid_state_log_no_dup lM mM: valid_state lM mM -> NoDup lM.
  Proof. intros Hvs; apply log_events_no_dup; apply Hvs. Qed.

 (** Local Validity. *)
  Definition mem_dom_local (M : gmap Key val) := dom M ⊆ DB_keys.

  Definition in_mem_log_some_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k v, M !! k = Some v → ∃ we, at_key k L = Some we ∧ we.(we_val) = v.

  Definition in_mem_log_none_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k, M !! k = None → at_key k L = None.

  Definition mem_serializable_vals_local (M : gmap Key val) :=
    ∀ k v, M !! k = Some v → Serializable DB_serialization v.

  Definition in_log_mem_some_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ we, at_key we.(we_key) L = Some we →  M !! we.(we_key) = Some we.(we_val).

  Definition in_log_mem_none_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k, at_key k L = None → M !! k = None.

  Definition allocated_in_mem_local (L : wrlog) (M : gmap Key val) :=
    ∀ l k we1, l ≤ₚ L → at_key k l = Some we1 → ∃ we2, M !! k = Some we2.(we_val) ∧ we1 ≤ₜ we2.

  Record valid_state_local (L : wrlog) (M : gmap Key val) : Prop :=
    {
      DB_LSTV_log_events : log_events L;
      DB_LSTV_mem_dom : mem_dom_local M;
      DB_LSTV_mem_serializable_vs_local : mem_serializable_vals_local M;
      DB_LSTV_in_mem_log_some_coh_local : in_mem_log_some_coh_local L M;
      DB_LSTV_in_mem_log_none_coh_local : in_mem_log_none_coh_local L M;
      DB_LSTV_in_log_mem_some_coh_local : in_log_mem_some_coh_local L M;
      DB_LSTV_in_log_mem_none_coh_local : in_log_mem_none_coh_local L M;
      DB_LSTV_mem_allocated_in_mem : allocated_in_mem_local L M;
    }.

  Lemma valid_state_local_empty : valid_state_local [] ∅.
  Proof.
    split; rewrite /mem_dom_local /in_mem_log_some_coh_local /in_mem_log_none_coh_local
                    /mem_serializable_vals_local /in_log_mem_some_coh_local /in_log_mem_none_coh_local
                  /allocated_in_mem_local /log_events;  try set_solver.
    - intros i Hin. rewrite nil_length in Hin. by lia.
    - intros l k we1 Hpre.
      destruct Hpre as (h2 & Hpre).
      symmetry in Hpre. apply app_eq_nil in Hpre. naive_solver.
  Qed.

  Lemma valid_state_local_update (lM : wrlog) (kvsMG : gmap Key val) wev :
    wev.(we_key) ∈ DB_keys →
    wev.(we_time) = length lM →
    Serializable DB_serialization wev.(we_val) →
    valid_state_local lM kvsMG ->
    valid_state_local (lM ++ [wev]) (<[wev.(we_key):= wev.(we_val)]> kvsMG).
  Proof.
    intros Hwevk Hwevt Hwevser Hvs.
    split.
    - apply log_events_state_update; [done|done|done|apply Hvs].
    - intros k; rewrite dom_insert elem_of_union elem_of_singleton; intros [->|Hk]; first done.
      apply Hvs; done.
    - intros k v.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite lookup_insert; intros; simplify_eq; done. }
      rewrite lookup_insert_ne; last done. apply Hvs.
    - intros k v.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite lookup_insert; intros; simplify_eq.
        rewrite at_key_snoc_some; eauto. }
      rewrite lookup_insert_ne; last done.
      rewrite at_key_snoc_none; last done.
      apply Hvs.
    - intros k.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite lookup_insert; done. }
      rewrite lookup_insert_ne; last done.
      rewrite at_key_snoc_none; last done.
      apply Hvs.
    - intros we.
      destruct (decide (we_key we = we_key wev)) as [->|].
      { rewrite at_key_snoc_some; last done. rewrite lookup_insert; intros; simplify_eq; done. }
      rewrite at_key_snoc_none; last done.
      rewrite lookup_insert_ne; last done.
      apply Hvs.
    - intros k.
      destruct (decide (k = we_key wev)) as [->|].
      { rewrite at_key_snoc_some; done. }
      rewrite lookup_insert_ne; last done.
      rewrite at_key_snoc_none; last done.
      apply Hvs.
    - intros l k wel Hl Hklwel.
      destruct (decide (k = we_key wev)) as [->|].
      + rewrite lookup_insert. eexists; split; first done.
        apply prefix_of_snoc in Hl as [->|Hl].
        { rewrite at_key_snoc_some in Hklwel; last done; simplify_eq.
          by right. (* this is weird; need to prove the Reflexive instance for ≤ₜ *) }
        assert (∃ i, lM !! i = Some wel) as [i Hi].
        { apply elem_of_list_lookup.
          eapply elem_of_prefix; last done.
          eapply at_key_elem_of; done. }
        apply lt_TM_lt.
        destruct (DB_LSTV_log_events _ _ Hvs i) as (?&Hi'&?&?&?);
          first by apply lookup_lt_is_Some_1; eauto.
        rewrite /TM_lt /=.
        rewrite Hi in Hi'; simplify_eq.
        rewrite Hwevt.
        apply lookup_lt_is_Some_1; eauto.
      + rewrite lookup_insert_ne; last done.
        apply prefix_of_snoc in Hl as [->|Hl].
        { rewrite at_key_snoc_none in Hklwel; last done; simplify_eq.
          eapply Hvs; done. }
        eapply Hvs; done.
  Qed.

  Lemma valid_state_local_log_no_dup lM mM: valid_state_local lM mM -> NoDup lM.
  Proof. intros Hvs; apply log_events_no_dup; apply Hvs. Qed.

End ValidStates.

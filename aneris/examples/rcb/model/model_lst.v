(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Export model_lhst.


Section Local_state_validity.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  Definition initial_time : vector_clock := (λ _, 0) <$> RCB_addresses.

  (** Local states *)
  Record Lst : Type :=
    LST {Lst_time : vector_clock; Lst_hst : gset local_event}.

  Definition empty_Lst : Lst := LST initial_time ∅.

  (** Valid Local states *)

  Definition RCBM_lst_time (t : vector_clock) (s : gset local_event) :=
    ∀ j, j < length RCB_addresses → t !! j = Some (lsec_sup j s).

  Definition RCBM_lst_hst_valid i s := RCBM_lhst_valid i s.

  Definition RCBM_lst_time_length (t : vector_clock) :=
    length t = length RCB_addresses.

  Record RCBM_Lst_valid (i : nat) (ls: Lst) : Prop :=
    {
      RCBM_LSTV_at : i < length RCB_addresses;

      (** Local Time *)
      RCBM_LSTV_time: RCBM_lst_time ls.(Lst_time) ls.(Lst_hst);

      RCBM_LSTV_time_length: RCBM_lst_time_length ls.(Lst_time);

      (** Local history *)
      RCBM_LSTV_hst_valid: RCBM_lst_hst_valid i ls.(Lst_hst);
   }.

  Global Arguments RCBM_LSTV_at {_ _} _.
  Global Arguments RCBM_LSTV_time {_ _} _.
  Global Arguments RCBM_LSTV_time_length {_ _} _.
  Global Arguments RCBM_LSTV_hst_valid {_ _} _.

  Lemma RCBM_Lst_valid_empty i :
    i < length RCB_addresses → RCBM_Lst_valid i empty_Lst.
  Proof.
    split;
      rewrite /RCBM_lst_time
              /RCBM_lst_time_length
              /RCBM_lst_hst_valid;
      [done| | |].
    - intros; rewrite /= lsec_sup_empty /initial_time list_lookup_fmap.
        by destruct (lookup_lt_is_Some_2 RCB_addresses j) as [? ->].
    - by rewrite /empty_Lst /= /initial_time fmap_length.
    - simpl. by apply empty_lhst_valid.
  Qed.

  Lemma RCBM_Lst_valid_time_le i ls e :
    RCBM_Lst_valid i ls →
    e ∈ ls.(Lst_hst) →
    vector_clock_le e.(le_time) ls.(Lst_time).
  Proof.
    intros Hls He.
    assert (length (le_time e) = length (Lst_time ls)) as Hlen.
    { erewrite RCBM_LSTV_time_length; eauto.
      erewrite <- RCBM_LHV_times; eauto using RCBM_LSTV_hst_valid.
      eapply RCBM_LSTV_hst_valid; eauto. }
    eapply Forall2_lookup; intros j.
    destruct (le_time e !! j) as [q|] eqn:Hq.
    - rewrite Hq.
      assert (j < length RCB_addresses).
      { erewrite <- RCBM_LHV_times; eauto using RCBM_LSTV_hst_valid.
        apply lookup_lt_is_Some; eauto.
         eauto using RCBM_LSTV_hst_valid.
         eapply RCBM_LSTV_hst_valid; eauto. }
      edestruct (lookup_lt_is_Some_2 (Lst_time ls) j) as [p Hp].
      { rewrite -Hlen.
        apply lookup_lt_is_Some; eauto. }
      rewrite Hp.
      constructor.
      erewrite RCBM_LSTV_time in Hp; eauto.
      simplify_eq.
      destruct (decide (j = le_orig e)) as [->|Heorig].
      + apply nat_sup_UB.
        apply elem_of_list_omap.
        eexists; split; first apply elem_of_elements;
          eauto using in_lsec_orig.
      + assert (RCBM_lsec_valid i (le_orig e) (Lst_hst ls)) as Hesec.
        { apply RCBM_LHV_secs_valid; first by apply RCBM_LSTV_hst_valid.
          eapply RCBM_LHV_origs; eauto using RCBM_LSTV_hst_valid;
            eapply RCBM_LSTV_hst_valid; eauto. }
        pose proof (RCBM_LSV_caus Hesec j e) as Hje.
        rewrite Hq /= in Hje.
        etrans; last apply nat_sup_mono.
        { apply Hje; auto using in_lsec_orig. }
        intros a (ae & [Hae11 Hae12]
                         %elem_of_list_filter & Hae2)%elem_of_list_omap.
        apply elem_of_list_omap; eauto.
    - rewrite Hq.
      apply lookup_ge_None in Hq.
      rewrite Hlen in Hq.
      apply lookup_ge_None in Hq.
      rewrite Hq.
      constructor.
  Qed.

  Lemma RCBM_Lst_valid_compute_maximals (i j : nat) (lst : Lst) (e : local_event) :
    RCBM_Lst_valid i lst ->
    e.(le_time) !! j = Some (S (default 0 (lst.(Lst_time) !! j))) ->
    e ∈ compute_maximals le_time (lst.(Lst_hst) ∪ {[ e ]}).
  Proof.
    intros [Hi ? ? ?] Htime_i.
    apply elem_of_list_to_set.
    apply elem_of_compute_maximals_as_list2; [set_solver |].
    intros e' Hin' Hcontra.
    assert (vector_clock_le e'.(le_time) lst.(Lst_time)) as Hle.
    { apply (RCBM_Lst_valid_time_le i); [done |].
      apply elem_of_union in Hin' as [? | Hr]; [done |].
      apply elem_of_singleton in Hr as ->.
      exfalso; apply vector_clock_lt_irreflexive in Hcontra; done. }
    pose proof (vector_clock_lt_le_trans _ _ _ Hcontra Hle) as Htrans.
    destruct Htrans as [Htrans _].
    rewrite /vector_clock_le in Htrans.
    assert (length e.(le_time) = length lst.(Lst_time)) as Hlen_eq.
    { eapply Forall2_length; done. }
    assert (j < length e.(le_time)) as Hlen_lt.
    { eapply lookup_lt_Some; done. }
    assert (∃ t, lst.(Lst_time) !! j = Some t) as [t Hsome].
    { apply lookup_lt_is_Some_2.
      rewrite -Hlen_eq; done. }
    rewrite Hsome in Htime_i; simpl in *.
    assert (S t <= t) as Hcontra'; [ | lia].
    by eapply Forall2_lookup_lr.
  Qed.

End Local_state_validity.

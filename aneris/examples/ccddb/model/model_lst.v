(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Export model_lhst.


Section Local_state_validity.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Definition lmem : Type := gmap Key val.

  Definition empty_lmem : lmem := ∅.

  Definition initial_time : vector_clock := (λ _, 0) <$> DB_addresses.

  (** Local states *)
  Record Lst : Type :=
    LST {Lst_mem : lmem; Lst_time : vector_clock; Lst_hst : gset apply_event}.

  Definition empty_Lst : Lst := LST empty_lmem initial_time ∅.

  (** Valid Local states *)

  Definition DBM_lst_dom_keys (d : lmem) := dom d ⊆ DB_keys.

  Definition DBM_lst_vals_Some (d : lmem) (s : gset apply_event) :=
    Eval simpl in
    ∀ k v, d !! k = Some v →
           let e := Observe_lhst (restrict_key k s) in
           v = e.(ae_val) ∧ e ∈ (compute_maximals ae_time (restrict_key k s)).

  Definition DBM_lst_vals_None (d : lmem) (s : gset apply_event) :=
    ∀ k, k ∈ DB_keys → d !! k = None ↔ restrict_key k s = ∅.

  Definition DBM_lst_time (t : vector_clock) (s : gset apply_event) :=
    ∀ j, j < length DB_addresses → t !! j = Some (lsec_sup j s).

  Definition DBM_lst_hst_valid i s := DBM_lhst_valid i s.

  Definition DBM_lst_time_length (t : vector_clock) :=
    length t = length DB_addresses.

  Record DBM_Lst_valid (i : nat) (ls: Lst) : Prop :=
    {
      DBM_LSTV_at : i < length DB_addresses;

      (** Domain *)
      DBM_LSTV_dom_keys: DBM_lst_dom_keys ls.(Lst_mem);

      (** Local memory *)
      DBM_LSTV_vals_Some: DBM_lst_vals_Some ls.(Lst_mem) ls.(Lst_hst);

      DBM_LSTV_vals_None: DBM_lst_vals_None ls.(Lst_mem) ls.(Lst_hst);

      (** Local Time *)
      DBM_LSTV_time: DBM_lst_time ls.(Lst_time) ls.(Lst_hst);

      DBM_LSTV_time_length: DBM_lst_time_length ls.(Lst_time);

      (** Local history *)
      DBM_LSTV_hst_valid: DBM_lst_hst_valid i ls.(Lst_hst);
   }.

  Global Arguments DBM_LSTV_at {_ _} _.
  Global Arguments DBM_LSTV_dom_keys {_ _} _.
  Global Arguments DBM_LSTV_vals_Some {_ _} _.
  Global Arguments DBM_LSTV_vals_None {_ _} _.
  Global Arguments DBM_LSTV_time {_ _} _.
  Global Arguments DBM_LSTV_time_length {_ _} _.
  Global Arguments DBM_LSTV_hst_valid {_ _} _.

  Lemma DBM_Lst_valid_empty i :
    i < length DB_addresses → DBM_Lst_valid i empty_Lst.
  Proof.
    split;
      rewrite /DBM_lst_dom_keys
              /DBM_lst_vals_Some
              /DBM_lst_vals_None
              /DBM_lst_time
              /DBM_lst_time_length
              /DBM_lst_hst_valid;
      [done|set_solver|set_solver|set_solver| | |].
    - intros; rewrite /= lsec_sup_empty /initial_time list_lookup_fmap.
        by destruct (lookup_lt_is_Some_2 DB_addresses j) as [? ->].
    - by rewrite /empty_Lst /= /initial_time fmap_length.
    - simpl. by apply empty_lhst_valid.
  Qed.

  Lemma DBM_Lst_valid_time_le i ls e :
    DBM_Lst_valid i ls →
    e ∈ ls.(Lst_hst) →
    vector_clock_le e.(ae_time) ls.(Lst_time).
  Proof.
    intros Hls He.
    assert (length (ae_time e) = length (Lst_time ls)) as Hlen.
    { erewrite DBM_LSTV_time_length; eauto.
      erewrite <- DBM_LHV_times; eauto using DBM_LSTV_hst_valid.
      eapply DBM_LSTV_hst_valid; eauto. }
    eapply Forall2_lookup; intros j.
    destruct (ae_time e !! j) as [q|] eqn:Hq.
    - rewrite Hq.
      assert (j < length DB_addresses).
      { erewrite <- DBM_LHV_times; eauto using DBM_LSTV_hst_valid.
        apply lookup_lt_is_Some; eauto.
         eauto using DBM_LSTV_hst_valid.
         eapply DBM_LSTV_hst_valid; eauto. }
      edestruct (lookup_lt_is_Some_2 (Lst_time ls) j) as [p Hp].
      { rewrite -Hlen.
        apply lookup_lt_is_Some; eauto. }
      rewrite Hp.
      constructor.
      erewrite DBM_LSTV_time in Hp; eauto.
      simplify_eq.
      destruct (decide (j = ae_orig e)) as [->|Heorig].
      + apply nat_sup_UB.
        apply elem_of_list_omap.
        eexists; split; first apply elem_of_elements;
          eauto using in_lsec_orig.
      + assert (DBM_lsec_valid i (ae_orig e) (Lst_hst ls)) as Hesec.
        { apply DBM_LHV_secs_valid; first by apply DBM_LSTV_hst_valid.
          eapply DBM_LHV_origs; eauto using DBM_LSTV_hst_valid;
            eapply DBM_LSTV_hst_valid; eauto. }
        pose proof (DBM_LSV_caus Hesec j e) as Hje.
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

End Local_state_validity.

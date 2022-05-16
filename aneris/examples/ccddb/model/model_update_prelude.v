From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_lst.

(** Global system validity preservation by Apply and Write updates. *)

Section Prelude.

  Context `{!anerisG Mdl Σ, !DB_params}.

  (* TODO: move restrict_key lemmas above somewhere in spec_util.v *)
  Lemma restrict_key_union k s1 s2 :
    restrict_key k (s1 ∪ s2) = restrict_key k s1 ∪ restrict_key k s2.
  Proof.
    apply set_eq; intros e.
    rewrite elem_of_union !elem_of_filter; set_solver.
  Qed.

  Lemma restrict_key_singleton_in k e :
    ae_key e = k → restrict_key k {[e]} = {[e]}.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite !elem_of_filter; set_solver.
  Qed.

  Lemma restrict_key_singleton_out k e :
    ae_key e ≠ k → restrict_key k {[e]} = ∅.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite  !elem_of_filter; set_solver.
  Qed.

  Definition update_condition i e t :=
    i < length DB_addresses ∧
    length t = length DB_addresses ∧
    length e.(ae_time) = length DB_addresses ∧
    e.(ae_key) ∈ DB_keys ∧
    e.(ae_orig) < length DB_addresses ∧
    e.(ae_time) !! e.(ae_orig) = Some (S (default 0 (t !! e.(ae_orig)))) ∧
    (∀ j, j < length DB_addresses → j ≠ e.(ae_orig) →
          default 0 (e.(ae_time) !! j) <= default 0 (t !! j)) ∧
    (e.(ae_orig) = i → e.(ae_time) = incr_time t i).

  Lemma update_condition_absurd i e : ¬ update_condition i e (ae_time e).
  Proof.
    destruct 1 as (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
    destruct (lookup_lt_is_Some_2 (ae_time e) (ae_orig e)) as [ti Hti];
      first eauto with lia.
    rewrite Hti in Het. inversion Het. lia.
  Qed.

  Lemma update_condition_time i e t:
    update_condition i e t → ¬ vector_clock_lt e.(ae_time) t.
  Proof.
    intros (?&?&?&?&?&Het&?&?) [Hle Hlt].
    eapply Forall2_lookup_l in Hle as (y & Hy1 & Hy2); last apply Het.
    rewrite Hy1 /= in Hy2; lia.
  Qed.

  Lemma update_condition_time_wr e t:
    update_condition e.(ae_orig) e t →
    vector_clock_lt t e.(ae_time).
  Proof.
    intros (Hi & ? & ? & Heln & Htlen & Heteq & Hetle & Heti).
    specialize (Heti eq_refl) as ->.
    apply incr_time_lt; lia.
  Qed.


  Lemma DBM_system_update_fresh_lhst e j t (s : gset apply_event) :
    (j < length t) →
    (∀ e, e ∈ s → vector_clock_lt t e.(ae_time) → False) →
    e.(ae_time) = (incr_time t j) →
    e ∉ s.
  Proof.
    intros Hjt Hst Htime Habs.
    apply incr_time_lt in Hjt.
    apply (Hst e Habs); rewrite Htime; done.
  Qed.

  Lemma update_condition_lhst_not_in e i t (s : gset apply_event) :
    (i < length t) →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    update_condition i e t →
    e ∉ s.
  Proof.
    intros Hjt Hst Hcnd Habs.
    apply (update_condition_time _ _ _ Hcnd).
    specialize (Hst e Habs).
    apply vector_clock_le_eq_or_lt in Hst as [ | ]; last done.
    subst t.
    by apply update_condition_absurd in Hcnd.
  Qed.

  Lemma update_condition_write (e : apply_event) (i : nat) (ls : Lst) :
    DBM_Lst_valid i ls →
    e.(ae_key) ∈ DB_keys →
    e.(ae_seqid) = S (size ls.(Lst_hst)) →
    e.(ae_time) = incr_time ls.(Lst_time) i →
    e.(ae_orig) = i →
    update_condition i e (Lst_time ls).
  Proof.
    intros Hvl Hek Heq Het Heo.
    pose proof (DBM_LSTV_at Hvl) as Hi.
    repeat split; intros; simpl; eauto.
      - eapply DBM_LSTV_time_length; eauto.
      - rewrite Het.  erewrite incr_time_length.
        eapply DBM_LSTV_time_length; eauto.
      - by rewrite Heo.
      - rewrite Het Heo. eapply incr_time_proj.
        destruct (lookup_lt_is_Some_2 (Lst_time ls) i) as [ti Hti].
        erewrite DBM_LSTV_time_length; eauto.
        rewrite -nth_lookup.
        pose proof (nth_lookup_Some (Lst_time ls) i 0 ti Hti) as Hnth.
          by rewrite Hnth.
      - rewrite Het. erewrite incr_time_proj_neq; eauto with lia.
  Qed.

End Prelude.

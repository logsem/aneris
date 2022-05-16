From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import events model_lst.

(** Global system validity preservation by Apply and Write updates. *)

Section Prelude.

  Context `{!anerisG Mdl Σ, !RCB_params}.

  Definition update_condition i e t :=
    i < length RCB_addresses ∧
    length t = length RCB_addresses ∧
    length e.(le_time) = length RCB_addresses ∧
    e.(le_orig) < length RCB_addresses ∧
    e.(le_time) !! e.(le_orig) = Some (S (default 0 (t !! e.(le_orig)))) ∧
    (∀ j, j < length RCB_addresses → j ≠ e.(le_orig) →
          default 0 (e.(le_time) !! j) <= default 0 (t !! j)) ∧
    (e.(le_orig) = i → e.(le_time) = incr_time t i).

  Lemma update_condition_absurd i e : ¬ update_condition i e (le_time e).
  Proof.
    destruct 1 as (Hi & Htlen & Hetlen & Heorig & Het & Het' & Het'').
    destruct (lookup_lt_is_Some_2 (le_time e) (le_orig e)) as [ti Hti];
      first eauto with lia.
    rewrite Hti in Het. inversion Het. lia.
  Qed.

  Lemma update_condition_time i e t:
    update_condition i e t → ¬ vector_clock_lt e.(le_time) t.
  Proof.
    intros (?&?&?&?&Het&?&?) [Hle Hlt].
    eapply Forall2_lookup_l in Hle as (y & Hy1 & Hy2); last apply Het.
    rewrite Hy1 /= in Hy2; lia.
  Qed.

  Lemma update_condition_time_wr e t:
    update_condition e.(le_orig) e t →
    vector_clock_lt t e.(le_time).
  Proof.
    intros (Hi & ? & Heln & Htlen & Heteq & Hetle & Heti).
    specialize (Heti eq_refl) as ->.
    apply incr_time_lt; lia.
  Qed.

  Lemma RCBM_system_update_fresh_lhst e j t (s : gset local_event) :
    (j < length t) →
    (∀ e, e ∈ s → vector_clock_lt t e.(le_time) → False) →
    e.(le_time) = (incr_time t j) →
    e ∉ s.
  Proof.
    intros Hjt Hst Htime Habs.
    apply incr_time_lt in Hjt.
    apply (Hst e Habs); rewrite Htime; done.
  Qed.

  Lemma update_condition_lhst_not_in e i t (s : gset local_event) :
    (i < length t) →
    (∀ e, e ∈ s → vector_clock_le e.(le_time) t) →
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

  Lemma update_condition_write (e : local_event) (i : nat) (ls : Lst) :
    RCBM_Lst_valid i ls →
    e.(le_seqid) = S (size ls.(Lst_hst)) →
    e.(le_time) = incr_time ls.(Lst_time) i →
    e.(le_orig) = i →
    update_condition i e (Lst_time ls).
  Proof.
    intros Hvl Heq Het Heo.
    pose proof (RCBM_LSTV_at Hvl) as Hi.
    repeat split; intros; simpl; eauto.
      - eapply RCBM_LSTV_time_length; eauto.
      - rewrite Het.  erewrite incr_time_length.
        eapply RCBM_LSTV_time_length; eauto.
      - by rewrite Heo.
      - rewrite Het Heo. eapply incr_time_proj.
        destruct (lookup_lt_is_Some_2 (Lst_time ls) i) as [ti Hti].
        erewrite RCBM_LSTV_time_length; eauto.
        rewrite -nth_lookup.
        pose proof (nth_lookup_Some (Lst_time ls) i 0 ti Hti) as Hnth.
          by rewrite Hnth.
      - rewrite Het. erewrite incr_time_proj_neq; eauto with lia.
  Qed.

End Prelude.

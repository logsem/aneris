From aneris.aneris_lang Require Import lang.
From aneris.examples.dscm.spec Require Import base time stdpp_utils.

(** Write and apply events *)

Section Events.
  Context `{!DB_time}.

  Class DB_events :=
    {
      (** Write events *)
      we : Type;
      WE_key : we -> Key;
      WE_val : we → val;
      WE_timed :> Timed we;
      WE_origin : we -> socket_address;
      WE_EqDecision :> EqDecision we;
      WE_Countable :> Countable we;
    }.

End Events.

Notation ghst := (list we).
Notation "h ≤ₚ h'" := (h `prefix_of` h') (at level 20).


Section Events_lemmas.
  Context `{!DB_time, !DB_events}.

  Definition mval : Type := val * Time * socket_address.

  Definition hist_at_key (k : Key) (h : ghst) : ghst :=
    filter (λ x, WE_key x = k) h.

  Definition at_key (k : Key) (h : ghst) : option we :=
    last (hist_at_key k h).

  Definition hist_at_origin (sa : socket_address) (h : ghst) : ghst :=
    filter (λ x, WE_origin x = sa) h.

  Definition at_origin (sa : socket_address) (h : ghst) : option we :=
    last (hist_at_origin sa h).

  Definition mval_of_we (e : we) := (WE_val e, WE_timed e, WE_origin e).
  Definition mval_of_we_opt (e : option we) : option mval :=
    from_option (λ we, Some $ mval_of_we we) None e.

  Lemma last_snoc_inv {A:Type} (l : list A) e:
    last l = Some e → ∃ l', l = l' ++ [e].
  Proof.
    intros Hl. induction l as [| x l IHl]; first done.
    destruct l as [ | y l'].
    - simpl in *. exists []. by list_simplifier.
    - rewrite last_cons_cons in Hl. specialize (IHl Hl).
      destruct IHl as (l'' & Hl'').
      rewrite Hl''. by exists (x :: l'').
  Qed.

  Lemma at_key_singleton (e : we) : at_key (WE_key e) [e] = Some e.
  Proof. rewrite -last_singleton /at_key /hist_at_key. f_equal.
         by rewrite filter_cons_True.
  Qed.

  Lemma hist_at_key_app k h1 h2 :
    hist_at_key k (h1 ++ h2) = hist_at_key k h1 ++ hist_at_key k h2.
  Proof.
    rewrite /hist_at_key.
    by rewrite filter_app.
  Qed.

  Lemma hist_at_key_singleton k e:
    hist_at_key k [e] = [e] ↔ at_key k [e] = Some e.
  Proof.
    split; intros Hh.
    rewrite -last_singleton /at_key.
    - by rewrite Hh.
    - rewrite /at_key in Hh.
      rewrite /hist_at_key.
      rewrite /hist_at_key in Hh.
      erewrite filter_cons_True; first done.
      rewrite filter_cons in Hh.
      by destruct ((decide (WE_key e = k))).
  Qed.

 Lemma hist_at_key_none_singleton k e:
   WE_key e ≠ k →
   hist_at_key k [e] = [].
 Proof.
   intros Hne.
   rewrite /hist_at_key.
   by rewrite filter_cons_False.
   Qed.

 Lemma hist_at_key_some_singleton k e:
   WE_key e = k →
   hist_at_key k [e] = [e].
 Proof.
   intros He.
   rewrite /hist_at_key.
   by rewrite filter_cons_True.
   Qed.

 Lemma hist_at_key_empty k :
    hist_at_key k [] = [].
  Proof. naive_solver. Qed.

  Lemma hist_at_key_empty_at_key k h:
    hist_at_key k h = [] ↔ at_key k h = None.
  Proof.
    rewrite /at_key; split; intros Hh.
    by rewrite Hh.
    by apply last_None in Hh.
  Qed.

  Lemma hist_at_key_frame_r_singleton k h e :
    WE_key e ≠ k →
    hist_at_key k (h ++ [e]) = hist_at_key k h.
  Proof.
    intros Hnek.
    rewrite hist_at_key_app.
    apply hist_at_key_none_singleton in Hnek as ->.
    by list_simplifier.
  Qed.

  Lemma hist_at_key_frame_r_suffix k h hf :
    at_key k hf = None →
    hist_at_key k (h ++ hf) = hist_at_key k h.
  Proof.
    intros Hnone.
    rewrite hist_at_key_app.
    apply hist_at_key_empty_at_key in Hnone as ->.
    by list_simplifier.
  Qed.

 Lemma hist_at_key_frame_l_singleton k h e :
    WE_key e ≠ k →
    hist_at_key k ([e] ++ h) = hist_at_key k h.
  Proof.
    intros Hnek.
    rewrite hist_at_key_app.
    apply hist_at_key_none_singleton in Hnek as ->.
    by list_simplifier.
  Qed.

 Lemma hist_at_key_frame_l_prefix k h hf :
    at_key k hf = None →
    hist_at_key k (hf ++ h) = hist_at_key k h.
  Proof.
    intros Hnone.
    rewrite hist_at_key_app.
    apply hist_at_key_empty_at_key in Hnone as ->.
    by list_simplifier.
  Qed.

  Lemma hist_at_key_add_r_singleton k h e :
    WE_key e = k →
    hist_at_key k (h ++ [e]) = hist_at_key k h ++ [e].
  Proof.
    intros Hek.
    rewrite hist_at_key_app.
    apply hist_at_key_some_singleton in Hek as ->.
    by list_simplifier.
  Qed.

 Lemma hist_at_key_add_l_singleton k h e :
    WE_key e = k →
    hist_at_key k ([e] ++ h) = [e] ++ hist_at_key k h.
  Proof.
    intros Hnek.
    rewrite hist_at_key_app.
    apply hist_at_key_some_singleton in Hnek as ->.
    by list_simplifier.
  Qed.

  Lemma at_key_snoc_none k h e :
    WE_key e ≠ k → at_key k (h ++ [e]) = at_key k h.
  Proof.
    intros Hk.
    rewrite /at_key.
    specialize (hist_at_key_frame_r_singleton k h _ Hk).
    intros Heq. by rewrite Heq.
  Qed.

 Lemma at_key_snoc_some k h e :
    WE_key e = k → at_key k (h ++ [e]) = Some e.
  Proof.
    intros Hk.
    rewrite /at_key.
    specialize (hist_at_key_add_r_singleton k h _ Hk).
    intros Heq. rewrite Heq. by rewrite last_snoc.
  Qed.

  Lemma obs_le_factor_common_prefix (h1 h2 h3 : list we) :
    (h1 ++ h2) ≤ₚ (h1 ++ h3) → h2 ≤ₚ h3.
  Proof.
    intros Hp. induction h1; first done.
    rewrite -!app_comm_cons in Hp.
    apply prefix_cons_inv_2 in Hp.  eauto.
  Qed.

  Lemma obs_le_factor_at_singleton (h1 h2 : list we) (e : we) :
    h1 ≠ [] → h1 ≤ₚ ([e] ++ h2) → ∃ h1', h1 = [e] ++ h1' ∧ h1' ≤ₚ h2.
  Proof.
    intros H1n Hp.
    destruct h1 eqn:Hh1; first done.
    apply prefix_cons_inv_1 in Hp as Heq.
    apply prefix_cons_inv_2 in Hp.
    naive_solver.
  Qed.

  Lemma hist_at_key_le_empty k h : [] ≤ₚ hist_at_key k h.
  Proof. by apply prefix_nil. Qed.

  Lemma obs_le_hist_at_key_le h1 h2 k :
    h1 ≤ₚ h2 → hist_at_key k h1 ≤ₚ hist_at_key k h2.
  Proof.
    generalize h2. induction h1.
    - rewrite hist_at_key_empty.
      intros. apply hist_at_key_le_empty.
    - clear h2. intros h2 Hle. destruct h2 eqn:Hh2.
      + by inversion Hle.
      + pose (prefix_cons_inv_1 a w _ _ Hle) as Heq.
        rewrite Heq. clear Heq.
        apply prefix_cons_inv_2 in Hle.
        specialize (IHh1 _ Hle).
        rewrite /hist_at_key.
        assert (w :: h1 = [w] ++ h1) as -> by naive_solver.
        assert (w :: l = [w] ++ l) as -> by naive_solver.
        rewrite !filter_app. apply prefix_app.
        naive_solver.
  Qed.

  Lemma obs_le_at_key_hist_at_key h1 hf h2 k :
    h2 = h1 ++ hf → hist_at_key k h1 = hist_at_key k h2 →
    hist_at_key k hf = [].
  Proof.
    intros Heq Hk. rewrite Heq in Hk.
    rewrite /hist_at_key in Hk. rewrite filter_app in Hk.
    rewrite {1}(app_nil_end (filter (λ x : we, WE_key x = k) h1)) in Hk.
    apply app_inv_head in Hk. symmetry in Hk. eauto.
  Qed.

  Lemma at_key_le_in k h1 h2 e :
    at_key k h1 = Some e →
    hist_at_key k h1 ≤ₚ hist_at_key k h2 →
    e ∈ hist_at_key k h2.
  Proof.
    intros Hkh1 Hle.
    destruct Hle as (hf & Hle').
    rewrite Hle'.
    rewrite /at_key in Hkh1.
    apply last_snoc_inv in Hkh1 as (l' & Hkh1).
    rewrite Hkh1. set_solver.
  Qed.


  Lemma mval_of_we_opt_at_key_none k h :
    hist_at_key k h = [] → mval_of_we_opt (at_key k h) = None.
  Proof.  rewrite /at_key.  by intros ->. Qed.

  Lemma mval_of_we_opt_at_key_some e k h :
    WE_key e = k →
    mval_of_we_opt (at_key k (h ++ [e])) = Some (mval_of_we e).
  Proof.
    intros He.
    rewrite /at_key /hist_at_key.
    rewrite filter_app.
    simpl.
    assert (filter (λ x : we, WE_key x = k) [e] = [e]) as ->.
    { by apply filter_cons_True with (l:=[]). }
    by rewrite last_snoc.
  Qed.

  Lemma at_key_hist_at_key_inv k h e :
    at_key k h = Some e →
    ∃ hl hr, h = hl ++ [e] ++ hr ∧ hist_at_key k hr = [].
  Proof.
    intros Hk.
    rewrite /at_key /hist_at_key in Hk.
    apply last_filter_postfix in Hk.
    destruct Hk as (ys & zs & -> & Hk).
    exists ys, zs.
    split; [done|].
    induction zs as [|z zs IHzs]; [done|].
    apply Forall_cons in Hk.
    destruct Hk as [Hz Hk].
    specialize (IHzs Hk).
    by rewrite /hist_at_key filter_cons_False.
  Qed.

  Lemma at_origin_hist_at_origin_inv sa h e :
    at_origin sa h = Some e →
    ∃ hl hr, h = hl ++ [e] ++ hr ∧ hist_at_origin sa hr = [].
  Proof.
    intros Hk.
    rewrite /at_key /hist_at_key in Hk.
    apply last_filter_postfix in Hk.
    destruct Hk as (ys & zs & -> & Hk).
    exists ys, zs.
    split; [done|].
    induction zs as [|z zs IHzs]; [done|].
    apply Forall_cons in Hk.
    destruct Hk as [Hz Hk].
    specialize (IHzs Hk).
    by rewrite /hist_at_origin filter_cons_False.
  Qed.

  Lemma at_key_has_key k h we :
    at_key k h = Some we → WE_key we = k.
  Proof.
    intros Hatkey. apply last_Some_elem_of, elem_of_list_filter in Hatkey.
    by destruct Hatkey as [Hatkey _].
  Qed.

  Lemma at_origin_has_origin sa h we :
    at_origin sa h = Some we → WE_origin we = sa.
  Proof.
    intros Hatorigin. apply last_Some_elem_of, elem_of_list_filter in Hatorigin.
    by destruct Hatorigin as [Hatorigin _].
  Qed.

End Events_lemmas.

From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.prelude Require Import misc strings.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import list_proof set_proof .
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
     Require Import semi_join_lattices model params.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.proof
     Require Import events spec.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.examples.gcounter
     Require Import gcounter_code_wrapper gcounter_proof.
From aneris.examples.crdt.statelib.examples.prod_comb
     Require Import prod_comb_code prod_comb_proof.
From aneris.examples.crdt.statelib.examples.pncounter
     Require Import pncounter_code_wrapper.


Section pn_cpt_proof.
  (* PN counter operations are either (n, 0) if we're adding n, or
     (0, m) if we're substracting m *)
  Definition pnctr_op_pred (o : gctr_op * gctr_op): bool :=
    match o with
    | (n1, n2) => (n1 =? 0) || (n2 =? 0)
    end.

  Context `{!anerisG M Σ, !CRDT_Params, !StLib_Res (prodOp gctr_op gctr_op pnctr_op_pred)}.

  Notation pnOp := (prodOp gctr_op gctr_op pnctr_op_pred).
  Notation pnSt := (prodSt gctr_st gctr_st).
  Notation pnParams := (prod_params gctr_op gctr_st gctr_op gctr_st pnctr_op_pred).

  Lemma pn_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_init_st.
  Proof.
    iApply (prod_init_st_fn_spec $! gctr_init_st_fn_spec gctr_init_st_fn_spec).  Qed.

  Lemma pn_cpt_mutator_spec :
    ⊢ @mutator_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_mutator.
  Proof.
    by iApply (prod_mutator_st_spec $! gctr_mutator_spec gctr_mutator_spec).
  Qed.

  Lemma pn_cpt_merge_spec :
    ⊢ @merge_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_merge.
  Proof.
    by iApply (prod_merge_st_spec $! gctr_merge_spec gctr_merge_spec).
  Qed.

  Lemma pn_crdt_fun_spec :
    ⊢ @crdt_fun_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_crdt.
  Proof.
    iApply (prod_crdt_fun_spec $! gctr_crdt_fun_spec gctr_crdt_fun_spec).
  Qed.

  Lemma pn_init_spec :
    @init_spec
      _ _ _ _ _ _ _ _ _ pnParams _
      (statelib_init
         (prod_ser
            (gctr_params.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_ser)
            (gctr_params.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_ser))
         (prod_deser
            (gctr_params.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_deser)
            (gctr_params.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_deser))) -∗
    @init_spec_for_specific_crdt
      _ _ _ _ _ _ _ _ _ _ _
       pn_cpt_init.
  Proof.
    iIntros "#Hinit".
    by iApply (prod_init_spec $! gctr_crdt_fun_spec gctr_crdt_fun_spec with "[$Hinit]").
  Qed.

End pn_cpt_proof.

Section Util.
  Context `{!anerisG M Σ}.

  Lemma wp_list_int_sum (l : list nat) lv ip :
    {{{ ⌜is_list l lv⌝ }}}
      list_int_sum lv  @[ip]
    {{{ (n : nat),  RET #n; ⌜n = list_sum l⌝ }}}.
  Proof.
    iIntros (Φ) "%Hlst HΦ".
    rewrite /list_int_sum. wp_lam. wp_pure _.
    iApply (@wp_list_fold _ _ _ _ _
                (λ (l0 : list nat) (acc : val), ⌜∃ (n : nat), acc = #n ∧ n = list_sum l0⌝)%I
                (λ n, True)%I (λ n, True)%I ip (λ: "acc" "n", "acc" + "n") l #0 lv with "[] []").
    - iIntros (n nv lacc lrem) "!#".
      iIntros (Ψ) "(%Hl & ((%m & -> & ->) & _)) HΨ".
      wp_pures.
      iApply "HΨ".
      iPureIntro. split; last done.
       replace (list_sum lacc + n)%Z with ((list_sum lacc + n)%nat : Z); last lia.
       exists ((list_sum lacc + n)%nat). split; eauto with lia.
       rewrite list_sum_app. simpl. eauto with lia.
    - iPureIntro. simpl. split_and!; try eauto. exists 0%nat; done.
    - iModIntro. iIntros (v) "((%n & -> & ->) & _)".
      by iApply "HΦ".
  Qed.

End Util.

Section pncounter_denot.

  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.

  Inductive CtrOp :=
  | Add (z : Z) : CtrOp.

  Definition ctr_payload (op : CtrOp) : Z :=
    match op with
    | Add z => z
    end.

  Global Instance ctr_op_eqdecision : EqDecision CtrOp.
  Proof. solve_decision. Qed.

  Global Instance ctr_op_countable : Countable CtrOp.
  Proof.
    refine {|
      encode op := match op with Add z => encode z end;
      decode n := Add <$> @decode Z _ _ n;
    |}.
    intros []. rewrite decode_encode /=. done.
  Qed.

  Definition CtrSt := Z.
  (* Context `{!Log_Time}. *)

  (* The value of a counter is just the sum of the operations' payloads. *)
  Fixpoint ctr_value (s : list (Event CtrOp)) : Z :=
    match s with
    | [] => 0%Z
    | ev :: xs => (ctr_payload ev.(EV_Op) + ctr_value xs)%Z
    end.

  Definition ctr_denot (s : gset (Event CtrOp)) (st : CtrSt) : Prop :=
    st = ctr_value (elements s).

  Global Instance ctr_denot_fun : Rel2__Fun ctr_denot.
  Proof.
    constructor; unfold ctr_denot; intros; subst; done.
  Qed.

  Global Instance ctr_denot_instance : CrdtDenot CtrOp CtrSt := {
    crdt_denot := ctr_denot;
  }.

  Lemma ctr_value_singleton ev :
    ctr_value [ev] = ctr_payload (ev.(EV_Op)).
  Proof.
    unfold ctr_value. lia.
  Qed.

  Lemma ctr_value_cons ev l :
    ctr_value (ev :: l) = (ctr_payload ev.(EV_Op) + ctr_value l)%Z.
  Proof.
    simpl. auto.
  Qed.

  Lemma ctr_value_app (l l' : list (Event CtrOp)) :
    ctr_value (l ++ l') = (ctr_value l + ctr_value l')%Z.
  Proof.
    generalize dependent l'.
    induction l as [ | h t Ht]; intros l'; [done |].
    rewrite -app_comm_cons.
    do 2 rewrite ctr_value_cons.
    rewrite (Ht l'). lia.
  Qed.

  Lemma ctr_value_perm (l l' : list (Event CtrOp)) :
    Permutation l l' -> ctr_value l = ctr_value l'.
  Proof.
    generalize dependent l'.
    induction l as [ | h t Ht]; intros l' Hperm.
    - apply Permutation_nil in Hperm; subst; reflexivity.
    - rewrite ctr_value_cons.
      apply Permutation_sym in Hperm.
      pose proof Hperm as Hperm'.
      apply Permutation_vs_cons_inv in Hperm as [l1 [l2 ->]].
      apply Permutation_sym, Permutation_cons_app_inv, Ht in Hperm'.
      rewrite Hperm'.
      do 2 rewrite ctr_value_app.
      rewrite ctr_value_cons.
      lia.
  Qed.

End pncounter_denot.

Section pncounter_coh.

  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.

  Definition Ctr_Op_Coh := λ (op : CtrOp) v, match op with Add z => v = #z end.

  Lemma Ctr_Op_Coh_Inj (o1 o2 : CtrOp) (v : val) :
    Ctr_Op_Coh o1 v → Ctr_Op_Coh o2 v → o1 = o2.
  Proof. destruct o1; destruct o2; simpl; intros ? ?; simplify_eq; done. Qed.

  Lemma Ctr_Op_Coh_Ser (op : CtrOp) (v : val) :
    Ctr_Op_Coh op v → Serializable int_serialization v.
  Proof.
    destruct op; rewrite /Ctr_Op_Coh; intros ?; simplify_eq; apply _.
  Qed.

  Definition Ctr_St_Coh := λ (st : CtrSt) v, v = #st.


  Lemma Ctr_St_Coh_Inj st1 st2 v :
    Ctr_St_Coh st1 v → Ctr_St_Coh st2 v → st1 = st2.
  Proof. rewrite /Ctr_St_Coh. intros. by simplify_eq. Qed.

  Lemma Ctr_St_Coh_Ser (st : CtrSt) (v : val) :
    Ctr_St_Coh st v → Serializable int_serialization v.
  Proof. rewrite /Ctr_St_Coh; intros ?; simplify_eq; apply _. Qed.


  Global Instance Ctr_Coh_Params : @StLib_Coh_Params CtrOp CtrSt :=
  {|
    StLib_StSerialization := int_serialization;
    StLib_Op_Coh := Ctr_Op_Coh;
    StLib_Op_Coh_Inj := Ctr_Op_Coh_Inj;
    StLib_St_Coh := Ctr_St_Coh;
    StLib_St_Coh_Inj := Ctr_St_Coh_Inj;
    StLib_StCoh_Ser := Ctr_St_Coh_Ser
  |}.

End pncounter_coh.

Section pn_event_mapping.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.

  Notation pn_prod_Op := (prodOp gctr_op gctr_op pnctr_op_pred).

  Program Definition to_pn_op (z : Z) : pn_prod_Op :=
    match z return pn_prod_Op with
    | Z0 => exist _ (0, 0) _
    | Zpos p => exist _ (Pos.to_nat p, 0) _
    | Zneg p => exist _ (0, Pos.to_nat p) _
    end.
  Next Obligation. done. Defined.
  Next Obligation. by intros z n; simpl; rewrite orb_true_r. Defined.
  Next Obligation. done. Defined.

  Definition event_prod_of_Z (ev : Event CtrOp) : Event pn_prod_Op :=
    let z := ctr_payload ev.(EV_Op) in
    {| EV_Op := to_pn_op z;  EV_Orig := ev.(EV_Orig);  EV_Time := ev.(EV_Time) |}.

  Definition event_set_prod_of_Z (s : event_set CtrOp) : event_set pn_prod_Op :=
    gset_map (λ ev, event_prod_of_Z ev) s.

  Definition event_Z_of_prod (ev : Event pn_prod_Op) : Event CtrOp :=
    match ev.(EV_Op) with
    | exist _ (p,n) _ =>
        {| EV_Op := Add (p-n);  EV_Orig := ev.(EV_Orig);  EV_Time := ev.(EV_Time) |}
    end.

  Definition event_set_Z_of_prod (s : event_set pn_prod_Op) : event_set CtrOp :=
    gset_map (λ ev, event_Z_of_prod ev) s.

  Lemma event_prod_of_Z_eq_t e e' :
    e =_t e' → (event_prod_of_Z e =_t event_prod_of_Z e').
  Proof.
    intro Heq.
    destruct e, e'.
    by inversion Heq as [[Heq1 Heq2 Heq3]].
  Qed.

  Lemma event_prod_of_Z_eq e e' :
    e = e' → (event_prod_of_Z e = event_prod_of_Z e').
  Proof.
    intro Heq.
    rewrite Heq.
    done.
  Qed.

  Lemma to_pn_op_inj z z' : to_pn_op z = to_pn_op z' -> z = z'.
  Proof.
    intros Heq.
    destruct (to_pn_op z) as [[o1 o2] pf] eqn:to1.
    destruct (to_pn_op z') as [[o1' o2'] pf'] eqn:to2.
    destruct z; simpl in *; destruct z'; simpl in *;  simplify_eq /=; eauto with lia.
  Qed.

  Lemma event_prod_of_Z_eq_inv e e' :
    event_prod_of_Z e = event_prod_of_Z e' → e = e'.
  Proof.
    intro Heq.
    destruct e, e'.
    inversion Heq as [[Heq1 Heq2 Heq3]]. subst.
    destruct EV_Op, EV_Op0.
    do 2 f_equal. rewrite! /ctr_payload in Heq1.
    apply to_pn_op_inj; done.
  Qed.

  Lemma event_set_prod_of_Z_union s s' :
    event_set_prod_of_Z (s ∪ s') = event_set_prod_of_Z s ∪ event_set_prod_of_Z s'.
  Proof. by rewrite /event_set_prod_of_Z gset_map_union. Qed.

  Lemma event_set_prod_of_Z_in e s :
    e ∈ s → (event_prod_of_Z e ∈ event_set_prod_of_Z s).
  Proof.
    intro He.
    induction s as [| e' s Hs IH] using set_ind_L; first done.
    rewrite event_set_prod_of_Z_union.
    apply elem_of_union.
    destruct (bool_decide (e' = e)) eqn:Heq.
    - apply bool_decide_eq_true_1 in Heq as ->.
      left. rewrite /event_set_prod_of_Z gset_map_singleton.
      apply elem_of_singleton. set_solver.
    - right. apply IH.
      apply bool_decide_eq_false_1 in Heq. set_solver.
  Qed.

 Lemma event_set_prod_of_Z_in_inv e s :
    (event_prod_of_Z e ∈ event_set_prod_of_Z s) → e ∈ s.
  Proof.
    intro He.
    induction s as [| e' s Hs IH] using set_ind_L; first done.
    rewrite event_set_prod_of_Z_union in He.
    apply elem_of_union.
    destruct (bool_decide (e' = e)) eqn:Heq.
    - apply bool_decide_eq_true_1 in Heq as ->.
      left. set_solver.
    -  apply bool_decide_eq_false_1 in Heq.
       rewrite /event_set_prod_of_Z gset_map_singleton in He.
       apply elem_of_union in He as [He|He].
       -- apply elem_of_singleton in He.
          apply event_prod_of_Z_eq_inv in He.
          set_solver.
       -- right. by apply IH.
  Qed.

  Lemma event_set_prod_of_Z_inclusion s s' :
    event_set_prod_of_Z s ⊆ event_set_prod_of_Z s' → s ⊆ s'.
  Proof.
    intros Hsub.
    intros e He.
    apply event_set_prod_of_Z_in in He.
    assert (event_prod_of_Z e ∈ event_set_prod_of_Z s') as Hes'.
    eapply elem_of_weaken; by set_solver.
    by apply event_set_prod_of_Z_in_inv.
  Qed.

  Lemma event_set_prod_of_Z_events_total_order s:
    events_total_order (event_set_prod_of_Z s) →
    events_total_order s.
  Proof.
    intros Hs.
    intros e e' He He' Hneq Horig.
    edestruct (Hs (event_prod_of_Z e) (event_prod_of_Z e')); try set_solver.
    intro Hf.
    apply Hneq.
    by apply event_prod_of_Z_eq_inv.
  Qed.

  Lemma event_Z_of_prod_of_Z (e : Event CtrOp) :
    event_Z_of_prod (event_prod_of_Z e) = e.
  Proof.
    rewrite /event_prod_of_Z /event_Z_of_prod.
    simpl.
    destruct (ctr_payload (EV_Op e)) eqn:Hpayload; simpl.
    - assert ((0%nat - 0%nat) = 0)%Z as ->; [lia|].
      assert (EV_Op e = Add 0) as Hopeq.
      { destruct (EV_Op e).
        rewrite /ctr_payload in Hpayload.
        rewrite Hpayload.
        done. }
      rewrite <- Hopeq.
      destruct e; done.
    - assert ((Pos.to_nat p - 0%nat) = Z.pos p)%Z as ->; [lia|].
      destruct e; simpl; f_equal /=. rewrite /ctr_payload in Hpayload. destruct EV_Op. subst. by eauto.
    - assert ((0%nat - Pos.to_nat p) = Z.neg p)%Z as ->; [lia|].
      destruct e; simpl; f_equal /=. rewrite /ctr_payload in Hpayload. destruct EV_Op. subst. by eauto.
  Qed.

  Lemma event_prod_of_Z_of_prod (e : Event pn_prod_Op) :
    event_prod_of_Z (event_Z_of_prod e) = e.
  Proof.
    destruct e as [[[p n] pf] repId ts].
    rewrite /event_Z_of_prod.
    simpl.
    rewrite /event_prod_of_Z.
    simpl.
    assert (to_pn_op (p - n) = (p, n) ↾ pf) as ->; [|done].
    pose proof pf as pf'.
    rewrite /pnctr_op_pred in pf'.
    apply orb_prop_elim in pf'.
    destruct pf' as [Hl | Hr].
    - assert (p = 0) as ->.
      { rewrite Is_true_true in Hl.
        apply Nat.eqb_eq in Hl.
        done.
      }
      assert (0%nat - n = -n)%Z as -> by lia.
      rewrite /to_pn_op.
      destruct (decide (n = 0)) as [-> | Hne].
      { simpl.
        apply prodOp_val_eq.
        done. }
      assert (-n = Z.neg (Pos.of_nat n)) as ->.
      { rewrite -(Pos2Z.opp_pos (Pos.of_nat n)).
        f_equal.
        eauto with lia. }
      assert (Pos.to_nat (Pos.of_nat n) = n) as ->.
      { apply Nat2Pos.id.
        done. }
      apply prodOp_val_eq.
      done.
    - assert (n = 0) as ->.
      { rewrite Is_true_true in Hr.
        apply Nat.eqb_eq in Hr.
        done. }
      assert (p - 0%nat = p)%Z as -> by lia.
      rewrite /to_pn_op.
      destruct (decide (p = 0)) as [-> | Hne].
      { simpl.
        apply prodOp_val_eq; done. }
      assert (Z.of_nat p = Z.pos (Pos.of_nat p)) as ->.
      { eauto with lia. }
      apply prodOp_val_eq.
      simpl.
      f_equal.
      apply Nat2Pos.id.
      done.
  Qed.

  Lemma event_set_Z_of_prod_union s s' :
    event_set_Z_of_prod (s ∪ s') = event_set_Z_of_prod s ∪ event_set_Z_of_prod s'.
  Proof. by rewrite /event_set_Z_of_prod gset_map_union. Qed.

  Lemma event_set_Z_of_prod_singleton (e : Event pn_prod_Op) : (event_set_Z_of_prod {[e]}) = {[event_Z_of_prod e]}.
  Proof.
    rewrite /event_set_Z_of_prod.
    by rewrite gset_map_singleton.
  Qed.

  Lemma event_set_prod_of_Z_singleton (e : Event CtrOp) : (event_set_prod_of_Z {[e]}) = {[event_prod_of_Z e]}.
  Proof.
    rewrite /event_set_prod_of_Z.
    by rewrite gset_map_singleton.
  Qed.

  Lemma event_set_Z_of_prod_of_Z s :
    event_set_Z_of_prod (event_set_prod_of_Z s) = s.
  Proof.
    induction s as [| e' s Hs IH] using set_ind_L; first done.
    rewrite event_set_prod_of_Z_union.
    rewrite event_set_Z_of_prod_union.
    rewrite IH.
    rewrite event_set_prod_of_Z_singleton.
    rewrite event_set_Z_of_prod_singleton.
    by rewrite event_Z_of_prod_of_Z.
  Qed.

  Lemma event_set_prod_of_Z_of_prod s :
    event_set_prod_of_Z (event_set_Z_of_prod s) = s.
  Proof.
    induction s as [| e' s Hs IH] using set_ind_L; first done.
    rewrite event_set_Z_of_prod_union.
    rewrite event_set_prod_of_Z_union.
    rewrite IH.
    rewrite event_set_Z_of_prod_singleton.
    rewrite event_set_prod_of_Z_singleton.
    by rewrite event_prod_of_Z_of_prod.
  Qed.

  Lemma event_prod_of_Z_time e :
    time (event_prod_of_Z e) = time e.
  Proof. done. Qed.

  Lemma event_set_prod_of_Z_compute_maximals (s : event_set CtrOp) :
    maximality.compute_maximals (event_set_prod_of_Z s) =
    event_set_prod_of_Z (maximality.compute_maximals s).
  Proof.
    assert (∀ e, e ∈ maximality.compute_maximals (event_set_prod_of_Z s) <-> e ∈ event_set_prod_of_Z (maximality.compute_maximals s)) as Helem; [|set_solver].
    intros e; split; rewrite /maximality.compute_maximals; intros Hin.
    - rewrite elem_of_filter in Hin.
      destruct Hin as [Hmax Hin].
      rewrite /event_set_prod_of_Z in Hin.
      apply gset_map_correct2 in Hin as [a [-> Hin]].
      apply gset_map_correct1.
      apply elem_of_filter.
      split; [|done].
      intros e' Hin' Hnot.
      assert (event_prod_of_Z e' ∈ event_set_prod_of_Z s) as Hin''.
      { rewrite /event_set_prod_of_Z.
        apply gset_map_correct1; done. }
      pose proof (Hmax (event_prod_of_Z e') Hin'') as Hlt.
      simpl in Hlt.
      apply Hlt.
      do 2 rewrite event_prod_of_Z_time.
      done.
    - rewrite /event_set_prod_of_Z in Hin.
      apply gset_map_correct2 in Hin as [a [-> [Hfa Hin]%elem_of_filter]].
      apply elem_of_filter.
      split.
      + intros e' Hin' Hnot.
        rewrite /event_set_prod_of_Z in Hin'.
        apply gset_map_correct2 in Hin' as [a' [-> Hin'']].
        do 2 rewrite event_prod_of_Z_time in Hnot.
        pose proof (Hfa a' Hin'') as H'.
        simpl in H'.
        apply H'.
        done.
      + rewrite /event_set_prod_of_Z.
        apply gset_map_correct1; done.
  Qed.

  Definition event_semi_inst := @gset_semi_set (@Event timestamp_time (prodOp gctr_op gctr_op pnctr_op_pred)) _ _.

  Lemma gset_map_empty_inv (s : event_set CtrOp) : gset_map event_prod_of_Z s = ∅ -> s = ∅.
  Proof.
    intros Heq.
    rewrite /gset_map in Heq.
    rewrite mapset_eq in Heq.
    apply mapset_eq.
    intros x; split; intros Hin.
    - pose proof (Heq (event_prod_of_Z x)) as Heq'.
      apply Heq'.
      rewrite (elem_of_list_to_set (H3:=event_semi_inst)).
      apply elem_of_list_fmap_1.
      apply elem_of_elements.
      done.
    - inversion Hin.
  Qed.

  Lemma elements_gset_empty_inv {A} `{Countable A} `{EqDecision A} (s : gset A) : elements s = [] -> s = ∅.
  Proof.
    intros Helem.
    destruct (decide (s = ∅)) as [-> | Hnot]; [done|].
    exfalso.
    apply Hnot.
    (* why does this work? *)
    assert (∀ e, e ∈ s <-> e ∈ (∅ : gset A)); [ | set_solver].
    apply elements_empty_inv in Helem.
    done.
  Qed.

  Lemma gset_singleton_eq_elem {A} `{Countable A} `{EqDecision A} a b : ({[a]} : gset A) = ({[b]} : gset A) -> a = b.
  Proof.
    intros Heq.
    assert (a ∈ ({[b]} : gset A)).
    { rewrite -Heq.
      set_solver. }
    set_solver.
  Qed.

  Lemma event_set_maximal_helper e s1 s2p:
    (∀ x y : Event pn_prod_Op,
       x ∈ event_set_prod_of_Z s1 ∪ {[event_prod_of_Z e]} ∪ s2p
       → y ∈ event_set_prod_of_Z s1 ∪ {[event_prod_of_Z e]} ∪ s2p → x =_t y → x = y) →
    maximality.compute_maximum (event_set_prod_of_Z s1 ∪ {[event_prod_of_Z e]} ∪ s2p) =
      Some (event_prod_of_Z e) →
    maximality.compute_maximum (s1 ∪ {[e]} ∪ event_set_Z_of_prod s2p) = Some e.
  Proof.
    intros Hext Hmax.
    apply maximality.compute_maximum_correct in Hmax; last done.
    apply maximality.compute_maximum_correct.
    - intros x y Hx Hy Heq.
      apply event_prod_of_Z_eq_inv.
      apply Hext; try apply event_set_prod_of_Z_in; eauto;
      replace s2p with (event_set_prod_of_Z (event_set_Z_of_prod s2p));
           last by rewrite event_set_prod_of_Z_of_prod.
      -- rewrite -event_set_prod_of_Z_singleton.
         rewrite -!event_set_prod_of_Z_union.
         by apply event_set_prod_of_Z_in.
      -- by rewrite event_set_prod_of_Z_of_prod.
      -- rewrite -event_set_prod_of_Z_singleton.
         rewrite -!event_set_prod_of_Z_union.
         by apply event_set_prod_of_Z_in.
    - destruct Hmax as [Hm1 Hm2].
      split.
      -- rewrite -event_set_prod_of_Z_singleton in Hm1.
         rewrite -!event_set_prod_of_Z_union in Hm1.
         replace s2p with (event_set_prod_of_Z (event_set_Z_of_prod s2p)) in Hm1;
           last by rewrite event_set_prod_of_Z_of_prod.
         rewrite -!event_set_prod_of_Z_union in Hm1.
         by apply event_set_prod_of_Z_in_inv.
      -- intros e0 He0 Hneq.
         specialize (Hm2 (event_prod_of_Z e0)).
         rewrite -!event_prod_of_Z_time.
         apply Hm2.
         replace s2p with (event_set_prod_of_Z (event_set_Z_of_prod s2p));
           last by rewrite event_set_prod_of_Z_of_prod.
         rewrite -event_set_prod_of_Z_singleton.
         rewrite -!event_set_prod_of_Z_union.
         by apply event_set_prod_of_Z_in.
         intro.
         apply Hneq.
         by apply event_prod_of_Z_eq_inv.
  Qed.


  Lemma event_set_prod_of_Z_cc s1 s2 :
    event_set_prod_of_Z s1 ⊆_cc event_set_prod_of_Z s2 →
    s1 ⊆_cc s2.
  Proof.
    rewrite /causally_closed_subseteq.
    rewrite /causally_closed.
    intros (Hs & Hcc).
    split.
    - by apply event_set_prod_of_Z_inclusion.
    - intros e e' He He' Hle He''.
      apply event_set_prod_of_Z_in_inv.

      specialize (Hcc (event_prod_of_Z e) (event_prod_of_Z e')).
      apply Hcc; try apply event_set_prod_of_Z_in; eauto.
  Qed.

End pn_event_mapping.

Section pn_CRDT_Res_Mixin_mapping.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn : !CRDT_Res_Mixin M Σ (prodOp gctr_op gctr_op pnctr_op_pred)}.

  Global Program Instance pn_CRDT_Res : CRDT_Res_Mixin M Σ CtrOp :=
    {|
      GlobInv := pn.(GlobInv) ;
      GlobState s := (pn.(GlobState) (event_set_prod_of_Z s));
      GlobSnap s := (pn.(GlobSnap) (event_set_prod_of_Z s));
      LocState i s1 s2 := (pn.(LocState) i (event_set_prod_of_Z s1) (event_set_prod_of_Z s2));
      LocSnap i s1 s2 := (pn.(LocSnap) i (event_set_prod_of_Z s1) (event_set_prod_of_Z s2));
    |}.
  Next Obligation.
    iIntros (s s') "Hs".
    by iApply GlobState_Exclusive.
  Defined.
  Next Obligation.
    iIntros (i s1 s2 s1' s2') "Hs".
    by iApply LocState_Exclusive.
  Defined.
  Next Obligation.
    iIntros (E s HE) "#Hinv Hg".
    by iApply GlobState_TakeSnap; eauto.
  Defined.
  Next Obligation.
    iIntros (s s') "#Hs1 #Hs2". rewrite event_set_prod_of_Z_union.
    iApply GlobSnap_Union; eauto.
  Defined.
  Next Obligation.
    iIntros (E s s' HE) "#Hinv #Hsn Hs".
    iMod (pn.(GlobSnap_GlobState_Included) with "[//][][$Hs]") as "(%Hs & Hg)"; eauto.
    iModIntro. iFrame. iPureIntro.
    by apply event_set_prod_of_Z_inclusion.
  Defined.
  Next Obligation.
    iIntros (E s s' HE) "#Hinv #Hs #Hs'".
    iMod (pn.(GlobSnap_Ext)
                    E (event_set_prod_of_Z s) (event_set_prod_of_Z s')
                    HE with "[$][$][$]") as "%Hy".
    iModIntro.
    iPureIntro.
    intros e0 e0' He0 He0' Heq.
    apply event_prod_of_Z_eq_inv.
    set_solver.
  Defined.
  Next Obligation.
    iIntros (E s HE) "#Hinv #Hs".
    iMod (pn.(GlobSnap_TotalOrder)
               E (event_set_prod_of_Z s)
               HE with "[$][$]") as "%Hy".
    iModIntro.
    iPureIntro.
    by apply event_set_prod_of_Z_events_total_order.
  Defined.
  Next Obligation.
    iIntros (i s1 s2) "Hf".
    iIntros (e Hs1).
    simpl.
    iPoseProof (pn.(LocState_OwnOrig) with "[$Hf]") as "%Hf".
    specialize (Hf (event_prod_of_Z e)).
    simpl in *.
    iPureIntro.
    apply Hf.
    by apply event_set_prod_of_Z_in.
  Defined.
  Next Obligation.
    iIntros (i s1 s2) "Hf".
    iIntros (e Hs1).
    simpl.
    iPoseProof (pn.(LocState_ForeignOrig) with "[$Hf]") as "%Hf".
    specialize (Hf (event_prod_of_Z e)).
    simpl in *.
    iPureIntro.
    apply Hf.
    by apply event_set_prod_of_Z_in.
  Defined.
  Next Obligation.
    iIntros (i s1 s2) "Hf".
    iIntros (e Hs1).
    simpl.
    iPoseProof (pn.(LocSnap_OwnOrig) with "[$Hf]") as "%Hf".
    specialize (Hf (event_prod_of_Z e)).
    simpl in *.
    iPureIntro.
    apply Hf.
    by apply event_set_prod_of_Z_in.
  Defined.
  Next Obligation.
    iIntros (i s1 s2) "Hf".
    iIntros (e Hs1).
    simpl.
    iPoseProof (pn.(LocSnap_ForeignOrig) with "[$Hf]") as "%Hf".
    specialize (Hf (event_prod_of_Z e)).
    simpl in *.
    iPureIntro.
    apply Hf.
    by apply event_set_prod_of_Z_in.
  Defined.
  Next Obligation.
    iIntros (i s1 s2) "Hf".
    simpl.
    iPoseProof (pn.(LocState_TakeSnap) with "[$Hf]") as "(Hf1 & Hf2)".
    iFrame.
  Defined.
  Next Obligation.
    iIntros (E i s1 s2 s1' s2' HE) "#Hinv #Hs #Hs'".
    iMod (pn.(LocSnap_Union) E _ (event_set_prod_of_Z s1) _ _ _ HE
           with "[$][$][$]") as "Hsnap".
    iModIntro.
    rewrite !event_set_prod_of_Z_union.
    simpl.
    iFrame.
  Defined.
  Next Obligation.
    iIntros (E i s1 s2 s1' s2' HE) "#Hinv #Hs HLst".
    iMod (pn.(LocSnap_LocState_Included_CC) E _ (event_set_prod_of_Z s1) _ _ _ HE with "[$][$][$]")
      as "(%Hh & Hsnap)".
    iModIntro.
    iFrame.
    rewrite -!event_set_prod_of_Z_union in Hh.
    iPureIntro.
    by apply event_set_prod_of_Z_cc.
    Defined.
  Next Obligation.
    iIntros (E i i' s1 s2 s1' s2' HE) "#Hinv #Hs1 #Hs2".
    iMod (pn.(LocSnap_Ext) E _ _ (event_set_prod_of_Z s1) _ _ _ HE with "[$][$][$]")
      as "%Hh".
    iModIntro.
    rewrite -!event_set_prod_of_Z_union in Hh.
    iPureIntro.
    intros e e' He He' Heq.
    apply event_prod_of_Z_eq_inv.
    apply Hh; try apply event_set_prod_of_Z_in; eauto.
    Defined.
  Next Obligation.
    iIntros (E i s1 s2 e HE He) "#Hinv #Hs".
    iMod (pn.(LocSnap_GlobSnap_Provenance) E _ (event_set_prod_of_Z s1) _ _ HE with "[$][$]")
      as "(%es & #Hsnap & %Hd)".
    rewrite -!event_set_prod_of_Z_union.
    apply event_set_prod_of_Z_in; eauto.
    iModIntro.
    iExists (event_set_Z_of_prod es).
    rewrite event_set_prod_of_Z_of_prod.
    iFrame "#".
    iPureIntro.
    apply event_set_prod_of_Z_in_inv.
    by rewrite event_set_prod_of_Z_of_prod.
  Defined.
  Next Obligation.
    iIntros (E i s1 s2 h HE) "#Hinv HLst #Hg".
    iMod (pn.(LocState_GlobSnap_Provenance)
               E i (event_set_prod_of_Z s1) (event_set_prod_of_Z s2) (event_set_prod_of_Z h) HE
                with "[$][$HLst][$Hg]") as "(HLst & %Hp)".
    iModIntro.
    iFrame.
    iPureIntro.
    intros e He Horig.
    apply event_set_prod_of_Z_in_inv; eauto.
    apply Hp; last done.
    by apply event_set_prod_of_Z_in.
  Defined.
  Next Obligation.
    iIntros (E i s1 s2 h HE) "#Hinv HLst #Hg".
    iMod (pn.(LocState_GlobSnap_Causality)
               E i (event_set_prod_of_Z s1) (event_set_prod_of_Z s2) (event_set_prod_of_Z h) HE
                with "[$][$HLst][$Hg]") as "(HLst & %Hp)".
    iModIntro.
    iFrame.
    iPureIntro.
    intros a e Ha He Ht.
    rewrite -!event_set_prod_of_Z_union in Hp.
    apply event_set_prod_of_Z_in_inv.
    apply (Hp _ (event_prod_of_Z e)); last done.
    by apply event_set_prod_of_Z_in.
    by apply event_set_prod_of_Z_in.
  Defined.

End pn_CRDT_Res_Mixin_mapping.

Section pn_Res_mapping.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op pnctr_op_pred)}.

  Global Program Instance pn_Res : StLib_Res CtrOp :=
    {|
      StLib_CRDT_Res := pn_CRDT_Res;
      StLib_InitToken := pn_prod_Res.(StLib_InitToken);
      StLib_SocketProto := pn_prod_Res.(StLib_SocketProto);
    |}.

End pn_Res_mapping.

Section pn_prod_specs_def.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op pnctr_op_pred)}.

  Notation pn_prod_Op := (prodOp gctr_op gctr_op pnctr_op_pred).
  Notation pn_prod_St := (prodSt gctr_st gctr_st).
  Notation pn_prod_Params := (prod_params gctr_op gctr_st gctr_op gctr_st).

  Definition pn_prod_upd_spec :=
    (@update_spec
       pn_prod_Op pn_prod_St
       _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res).
  Definition pn_prod_get_state_spec :=
    (@get_state_spec
       pn_prod_Op pn_prod_St
       _ _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res).
  Definition pn_prod_init_crdt_spec :=
    @init_spec_for_specific_crdt
      pn_prod_Op pn_prod_St
      _ _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res.

End pn_prod_specs_def.

Section pn_specs_def.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_Res : !StLib_Res CtrOp}.

  Definition pn_get_state_spec :=
    (@get_state_spec
       CtrOp CtrSt _ _ _ _ _ _ _ Ctr_Coh_Params pn_Res).
  Definition pn_upd_spec :=
    @update_spec
      CtrOp CtrSt _ _ _ _ _ _ Ctr_Coh_Params pn_Res.
  Definition pn_init_crdt_spec :=
    @init_spec_for_specific_crdt
      CtrOp CtrSt _ _ _ _ _ _ _ Ctr_Coh_Params pn_Res.

End pn_specs_def.

Section pncounter_proof.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op pnctr_op_pred)}.

  Definition pnop_proof_left (n : nat) : pnctr_op_pred (n, 0).
  Proof.
    simpl.
    rewrite orb_true_r.
    done.
  Qed.

  Definition pnop_proof_right (n : nat) : pnctr_op_pred (0, n).
  Proof.
    done.
  Qed.

  Definition pnop_left (n : nat) : (prodOp _ _ pnctr_op_pred) :=
    (n, 0) ↾ (pnop_proof_left n).

  Definition pnop_right (n : nat) : (prodOp _ _ pnctr_op_pred) :=
    (0, n) ↾ (pnop_proof_right n).


  (* TODO: move to library *)
  Lemma gset_map_comp `{!EqDecision A, !Countable A, !EqDecision B, !Countable B, !EqDecision C, !Countable C}
    (f : A → B) (g : B → C) (s : gset A) :
    gset_map g (gset_map f s) = gset_map (g ∘ f) s.
  Proof.
    induction s as [|a s ? IHs] using set_ind_L.
    { rewrite !gset_map_empty//. }
    rewrite !gset_map_union !gset_map_singleton/= IHs//.
  Qed.
  Lemma gset_map_ext  `{!EqDecision A, !Countable A, !EqDecision B, !Countable B}
    (f g : A → B) (s : gset A) : (∀ x, f x = g x) → gset_map f s = gset_map g s.
  Proof.
    induction s as [|a s ? IHs] using set_ind_L; intros Hfg.
    { rewrite !gset_map_empty//. }
    rewrite !gset_map_union !gset_map_singleton/= IHs; last done.
    rewrite Hfg; done.
  Qed.

  (* Lemma fst_of_event_prod_nneg a : (0 ≤ EV_Op (event_map prodOp_fst (event_prod_of_Z a)))%Z. *)
  (* Proof. destruct a as [[[]] ? ?]; lia. Qed. *)

  (* Lemma snd_of_event_prod_nneg a : (0 ≤ EV_Op (event_map prodOp_snd (event_prod_of_Z a)))%Z. *)
  (* Proof. destruct a as [[[]] ? ?]; lia. Qed. *)

  (* (* this could probably be made more generally about elements and union which could also be useful for other purposes. *) *)
  (* Lemma ctr_value_elements (s1 s2 : event_set CtrOp) : *)
  (*   (∀ x, x ∈ s1 → (0 ≤ ctr_payload (EV_Op x))%Z) → *)
  (*   (ctr_value (elements (s1 ∪ s2)) ≤ ctr_value (elements s1) + ctr_value (elements s2))%Z. *)
  (* Proof. *)
  (*   revert s2; induction s1 as [|a s1 ? IHs1] using set_ind_L; intros s2 Hs1nneg. *)
  (*   { rewrite left_id_L elements_empty /=; lia. } *)
  (*   erewrite (ctr_value_perm (elements ({[a]} ∪ s1))); last apply elements_union_singleton; last done. *)
  (*   simpl. *)
  (*   assert (ctr_value (elements (s1 ∪ s2)) ≤ ctr_value (elements s1) + ctr_value (elements s2))%Z. *)
  (*   { apply IHs1; set_solver. } *)
  (*   assert (0 ≤ ctr_payload (EV_Op a))%Z by set_solver. *)
  (*   destruct (decide (a ∈ s1 ∪ s2)). *)
  (*   - replace ({[a]} ∪ s1 ∪ s2) with (s1 ∪ s2) by set_solver. *)
  (*     lia. *)
  (*   - rewrite -assoc_L. *)
  (*     erewrite (ctr_value_perm (elements ({[a]} ∪ _))); last apply elements_union_singleton; last done. *)
  (*     simpl; lia. *)
  (* Qed. *)

  Lemma ctr_value_sub_helper1 a s :
    a ∉ s →
    event_map (λ z : nat, Add z) (event_map prodOp_fst (event_prod_of_Z a)) ∈
    (gset_map (λ x, event_map
        (λ z : nat, Add z) (event_map prodOp_fst x)) (event_set_prod_of_Z s)) →
    EV_Op (event_map prodOp_fst (event_prod_of_Z a)) = 0 :> nat.
  Proof.
    intros Has.
    rewrite gset_map_comp; intros (z & Hz1 & Hz2)%gset_map_correct2.
    destruct a as [[a] ?]; simplify_eq/=.
    destruct z as [[z] ?]; simplify_eq/=.
    destruct a; destruct z; try done.
    rewrite /prodOp_fst /prodOp_val /= in Hz1.
    simplify_eq; set_solver.
  Qed.

  Lemma ctr_value_sub_helper2 a s :
    a ∉ s →
    event_map (λ z : nat, Add z) (event_map prodOp_snd (event_prod_of_Z a)) ∈
    (gset_map (λ x, event_map
        (λ z : nat, Add z) (event_map prodOp_snd x)) (event_set_prod_of_Z s)) →
    EV_Op (event_map prodOp_snd (event_prod_of_Z a)) = 0 :> nat.
  Proof.
    intros Has.
    rewrite gset_map_comp; intros (z & Hz1 & Hz2)%gset_map_correct2.
    destruct a as [[a] ?]; simplify_eq/=.
    destruct z as [[z] ?]; simplify_eq/=.
    destruct a; destruct z; try done.
    rewrite /prodOp_snd /prodOp_val /= in Hz1.
    simplify_eq; set_solver.
  Qed.

  Lemma ctr_value_sub_helper3 a (s : event_set CtrOp) :
    (a ∈ s → ctr_payload (EV_Op a) = 0) →
    (ctr_value (elements ({[a]} ∪ s)) = ctr_payload (EV_Op a) + ctr_value (elements s))%Z.
  Proof.
    intros Has.
    destruct (decide (a ∈ s)).
    - rewrite Has; last done.
      replace ({[a]} ∪ s) with s by set_solver.
      lia.
    - erewrite (ctr_value_perm (elements ({[a]} ∪ _))); last apply elements_union_singleton; done.
  Qed.

  Lemma ctr_value_sub_helper4 a :
    ctr_payload (EV_Op a) =
    ((prodOp_fst (to_pn_op (ctr_payload (EV_Op a)))) -
      (prodOp_snd (to_pn_op (ctr_payload (EV_Op a)))))%Z.
  Proof. destruct a as [[[]] ?]; rewrite /prodOp_fst /prodOp_snd /prodOp_val /=; lia. Qed.

  Definition fst_map s := (gset_map (λ x, event_map
                    (λ z : nat, Add z) (event_map prodOp_fst x)) (event_set_prod_of_Z s)).

  Lemma fst_map_union s1 s2 : fst_map (s1 ∪ s2) = fst_map s1 ∪ fst_map s2.
  Proof. rewrite /fst_map /event_set_prod_of_Z !gset_map_union //. Qed.

  Lemma fst_map_empty : fst_map ∅ = ∅.
  Proof. rewrite /fst_map /event_prod_of_Z gset_map_empty //. Qed.

  Lemma fst_map_singleton a :
    fst_map {[a]} = {[ event_map (λ z : nat, Add z) (event_map prodOp_fst (event_prod_of_Z a))]}.
  Proof. rewrite /fst_map /event_set_prod_of_Z !gset_map_singleton //. Qed.

  Definition snd_map s := (gset_map (λ x, event_map
                    (λ z : nat, Add z) (event_map prodOp_snd x)) (event_set_prod_of_Z s)).

  Lemma snd_map_union s1 s2 : snd_map (s1 ∪ s2) = snd_map s1 ∪ snd_map s2.
  Proof. rewrite /snd_map /event_set_prod_of_Z !gset_map_union //. Qed.

  Lemma snd_map_empty : snd_map ∅ = ∅.
  Proof. rewrite /snd_map /event_prod_of_Z gset_map_empty //. Qed.

  Lemma snd_map_singleton a :
    snd_map {[a]} = {[ event_map (λ z : nat, Add z) (event_map prodOp_snd (event_prod_of_Z a))]}.
  Proof. rewrite /snd_map /event_set_prod_of_Z !gset_map_singleton //. Qed.

  Lemma ctr_value_sub s :
    ctr_value (elements s) = (ctr_value (elements (fst_map s)) - ctr_value (elements (snd_map s)))%Z.
  Proof.
    induction s as [|a s] using set_ind_L.
    { rewrite fst_map_empty snd_map_empty //. }
    rewrite fst_map_union fst_map_singleton snd_map_union snd_map_singleton.
    erewrite (ctr_value_perm (elements ({[a]} ∪ _))); last apply elements_union_singleton; last done.
    rewrite ctr_value_sub_helper3; last first.
    { intros Heq%ctr_value_sub_helper1; last done.
      destruct a; simpl in *; rewrite Heq; lia. }
    rewrite ctr_value_sub_helper3; last first.
    { intros Heq%ctr_value_sub_helper2; last done.
      destruct a; simpl in *; rewrite Heq; lia. }
    rewrite /= {1}(ctr_value_sub_helper4 a).
    rewrite IHs. lia.
  Qed.

  Lemma ctr_value_fold_sum s :
    ctr_value (elements (gset_map (event_map (λ z : nat, Add z)) s)) = fold_sum s.
  Proof.
    apply (set_fold_ind_L (λ (n : nat) s, ctr_value (elements (gset_map (event_map (λ z : nat, Add z)) s)) = n)).
    { rewrite gset_map_empty elements_empty //. }
    clear s.
    intros a s n Has IHs.
    rewrite gset_map_union gset_map_singleton.
    erewrite (ctr_value_perm (elements (_ ∪ _))); last apply elements_union_singleton; last first.
    { intros (z & Hz1 & Hz2)%gset_map_correct2.
      destruct a as [a ?]; simplify_eq/=.
      destruct z as [z ?]; simplify_eq/=.
      set_solver. }
    rewrite /= IHs.
    destruct a; simpl; lia.
  Qed.

  Lemma list_sum_fold_sum n m (l : list nat) s :
    m ≤ n →
    (∀ a, a ∈ s → EV_Orig a < m) →
    length l = m →
    (∀ i, i < m → l !!! i = fold_sum (fil s i)) →
    list_sum l = fold_sum s.
  Proof.
    revert m l s; induction n as [|n IHn]; intros m l s Hle Horigs Hlen Heq.
    - destruct (set_choose_or_empty s) as [[x Hx]| ->].
      { specialize (Horigs x Hx); lia. }
      destruct l eqn:Hlv.
      { rewrite /= /fold_sum set_fold_empty //. }
      pose proof (f_equal length Hlv) as Hlen'.
      simpl in *; lia.
    - destruct l as [|a l _] using rev_ind.
      { simpl in *; subst.
        destruct (set_choose_or_empty s) as [[x Hx]| ->].
        - specialize (Horigs x Hx); lia.
        - rewrite /= /fold_sum set_fold_empty //. }
      rewrite list_sum_app /=.
      rewrite app_length /= in Hlen.
      specialize (IHn (length l) l (filter (λ ev : Event gctr_op, EV_Orig ev ≠ (length l)) s)).
      rewrite IHn; [|lia| |done|]; last first.
      { intros j Hj.
        specialize (Heq j).
        rewrite lookup_total_app_l in Heq; last done.
        rewrite Heq; last lia.
        rewrite /fil.
        f_equal.
        apply set_eq; intros ?; rewrite !elem_of_filter.
        split; last tauto.
        intros [-> ]; split_and!; [done|lia|done]. }
      { intros ?; rewrite elem_of_filter; intros [? Hin].
        apply Horigs in Hin; lia. }
      specialize (Heq (length l)).
      rewrite lookup_total_app_r in Heq; last lia.
      rewrite Nat.sub_diag /= in Heq.
      rewrite Heq; last lia.
      rewrite /fil.
      rewrite Nat.add_0_r.
      rewrite -fold_sum_disj_union_gen;
        last by symmetry; apply disjoint_filter_complement.
      rewrite comm_L.
      rewrite filter_union_complement_L; first done.
      apply inhabitant.
  Qed.

  (* TODO: Prove: *)
  (* Definition pncounter_eval : val := *)
  (*   λ: "get_state" <>, *)
  (*      let: "st" := "get_state" #() in *)
  (*      let: "pl" := Fst "st" in *)
  (*      let: "nl" := Snd "st" in *)
  (*      let: "p" := list_int_sum "pl" in *)
  (*      let: "n" := list_int_sum "nl" in *)
  (*      "p" - "n". *)
  Lemma pncounter_eval_spec (get_state_fn : val) repId addr:
    GlobInv ⊢
    pn_prod_get_state_spec get_state_fn repId addr -∗
    pn_get_state_spec (λ:<>, pncounter_eval get_state_fn #()) repId addr.
  Proof.
    rewrite /pn_prod_get_state_spec/get_state_spec.
    iIntros "#Hinv #Hspec".
    iIntros (Hin Φ) "!# Hvsh".
    wp_pures. wp_lam. wp_pures.
    wp_apply ("Hspec" $! Hin); try eauto.
    iMod "Hvsh".
    iDestruct "Hvsh" as (s1 s2) "(HLst & Hvsh)".
    iExists (event_set_prod_of_Z s1), (event_set_prod_of_Z s2).
    iFrame.
    iModIntro.
    iNext.
    iIntros (s2'p v lv) "(%Hsub & HLst & %Hcoh & %Hdenot)".
    rewrite /StLib_St_Coh /= /prodSt_coh in Hcoh.
    destruct lv as (lv1, lv2).
    rewrite /crdt_denot /= /prod_denot in Hdenot.
    destruct Hdenot as (Hdenot1 & Hdenot2).
    destruct Hcoh as (v1 & v2 & <- & Hcoh1 & Hcoh2).
    rewrite /StLib_St_Coh /= /gctr_st_coh in Hcoh1, Hcoh2.
    rewrite Hcoh1 Hcoh2.
    iAssert (⌜s2 ⊆ event_set_Z_of_prod s2'p⌝ ∗
               LocState repId s1 (event_set_Z_of_prod s2'p) ∗
               ⌜@StLib_St_Coh CtrOp _ Ctr_Coh_Params (list_sum lv1 - list_sum lv2)%Z
                #(list_sum lv1 - list_sum lv2)⌝ ∗
               ⌜@ctr_denot (s1 ∪ event_set_Z_of_prod s2'p)
                (list_sum lv1 - list_sum lv2)%Z⌝)%I
            with "[HLst]"
            as "Hh".
    { simpl.
      rewrite event_set_prod_of_Z_of_prod.
      iFrame.
      iPureIntro.
      split_and!; [|done|].
      - intros x Hx.
        apply event_set_prod_of_Z_in in Hx.
        assert (event_prod_of_Z x ∈ s2'p) as Hxs2p.
        { eapply elem_of_weaken; set_solver. }
        apply event_set_prod_of_Z_in_inv.
        by rewrite event_set_prod_of_Z_of_prod.
      - rewrite /ctr_denot.
        simpl in Hdenot1. rewrite /gctr_denot_prop in Hdenot1.
        simpl in Hdenot2. rewrite /gctr_denot_prop in Hdenot2.
        rewrite ctr_value_sub.
        f_equal.
        + rewrite /fst_map.
           transitivity (ctr_value
                           (elements
                              (gset_map (λ x, event_map (λ z : nat, Add z) x)
                                 (gset_map (λ x, event_map prodOp_fst x)
                                 (event_set_prod_of_Z (s1 ∪ event_set_Z_of_prod s2'p))))));
           last by rewrite gset_map_comp; f_equal.
          rewrite ctr_value_fold_sum.
          erewrite (list_sum_fold_sum (length CRDT_Addresses) (length CRDT_Addresses));
            [done|reflexivity| |by rewrite vec_to_list_length|].
          * admit.
          * intros i Hi.
            specialize (Hdenot1 (nat_to_fin Hi)).
            apply vlookup_lookup in Hdenot1.
            rewrite fin_to_nat_to_fin in Hdenot1.
            apply list_lookup_total_correct in Hdenot1.
            rewrite Hdenot1.
            repeat f_equal.
            rewrite event_set_prod_of_Z_union event_set_prod_of_Z_of_prod //.
        + rewrite /fst_map.
           transitivity (ctr_value
                           (elements
                              (gset_map (λ x, event_map (λ z : nat, Add z) x)
                                 (gset_map (λ x, event_map prodOp_snd x)
                                 (event_set_prod_of_Z (s1 ∪ event_set_Z_of_prod s2'p))))));
           last by rewrite gset_map_comp; f_equal.
          rewrite ctr_value_fold_sum.
          erewrite (list_sum_fold_sum (length CRDT_Addresses) (length CRDT_Addresses));
            [done|reflexivity| |by rewrite vec_to_list_length|].
          * admit.
          * intros i Hi.
            specialize (Hdenot2 (nat_to_fin Hi)).
            apply vlookup_lookup in Hdenot2.
            rewrite fin_to_nat_to_fin in Hdenot2.
            apply list_lookup_total_correct in Hdenot2.
            rewrite Hdenot2.
            repeat f_equal.
            rewrite event_set_prod_of_Z_union event_set_prod_of_Z_of_prod //. }
    iMod ("Hvsh" $! (event_set_Z_of_prod s2'p)
                      #(list_sum lv1 - list_sum lv2)
                      (list_sum lv1 - list_sum lv2)%Z with "[$Hh]") as "HΦ".
    iModIntro.
    wp_pures.
    rewrite /gctr_st_inject.
    wp_apply (wp_list_int_sum lv1).
    { iPureIntro. apply is_list_inject; eauto. }
    iIntros (p ->).
    wp_pures.
    wp_apply (wp_list_int_sum lv2).
    { iPureIntro. apply is_list_inject; eauto. }
    iIntros (n ->).
    wp_pures.
    done.
  Admitted.

  (* TODO: Prove: *)
  (* Definition pncounter_update : val := *)
  (*   λ: "upd" "n", *)
  (*     (if: #0 ≤ "n" *)
  (*      then  "upd" ("n", #0) *)
  (*      else  "upd" (#0, (- "n"))). *)
  Lemma pncounter_update_spec (upd_fn : val) repId addr:
    GlobInv ⊢
    pn_prod_upd_spec upd_fn repId addr -∗
    pn_upd_spec (λ:"n", pncounter_update upd_fn "n") repId addr.
  Proof.
    rewrite /pn_prod_upd_spec/update_spec.
    iIntros "#Hinv #Hspec".
    iIntros (v op Hin Hcoh).
    destruct op.
    rewrite /StLib_Op_Coh /= /Ctr_Op_Coh in Hcoh.
    rewrite Hcoh.
    iModIntro.
    iIntros (Φ) "Hvsh".
    wp_pures. wp_lam. wp_pures.
    case_bool_decide as Hz; wp_pures.
    - wp_apply ("Hspec" $! (#z, #0)%V (pnop_left (Z.to_nat z)) ); try eauto.
      -- iPureIntro. simpl. rewrite /prodOp_coh /StLib_Op_Coh /= /gctr_op_coh /=.
         eexists #z, #0. split_and!; eauto.
         symmetry. f_equal. f_equal. by apply Z2Nat.id.
      -- iMod "Hvsh".
         iDestruct "Hvsh" as (h s1 s2) "((HGst & HLst) & Hvsh)".
         iExists (event_set_prod_of_Z h),
                   (event_set_prod_of_Z s1),
                     (event_set_prod_of_Z s2).
         iFrame.
         iModIntro.
         iNext.
         iIntros (ep hp s1p s2p)
                 "(%He1 & %He2 & %He3 & %He4 & %He5 & %He6 & %He7 & %He8 & %He9 & HGst & HLst)".
         iDestruct (LocState_TakeSnap with "HLst") as "(HLst & #Hsnap)".
         iMod (LocSnap_Ext
                         _ repId repId s1p s2p
                        with "[$][$][$]") as "%Hext";
             [solve_ndisj| ].
         iApply ("Hvsh" $!
                      (event_Z_of_prod ep)
                      (event_set_Z_of_prod hp)
                      (event_set_Z_of_prod s1p)
                      (event_set_Z_of_prod s2p)).
         simplify_eq /=.
         assert (∃ e, event_prod_of_Z e = ep) as Hf1.
         { exists {| EV_Op := Add (Z.to_nat z); EV_Orig := ep.(EV_Orig);  EV_Time := ep.(EV_Time) |}.
           rewrite /event_prod_of_Z. simplify_eq /=.
           destruct ep. f_equal /=.
           rewrite He1. simplify_eq /=.
           destruct (bool_decide (0 ≤ Z.to_nat z)%Z) eqn:Hle; simplify_eq /=; eauto with lia.
           - apply bool_decide_eq_true in Hle.
             destruct z; simplify_eq /=; rewrite /pnop_left;
                apply prodOp_val_eq; simpl; f_equal.
             replace (Z.of_nat (Z.to_nat (Z.pos p))) with (Z.pos p) by lia.
             simpl. f_equal.
           - apply bool_decide_eq_false in Hle; lia.
         }
         destruct Hf1 as (e & <-).
         replace ({[event_prod_of_Z e]}) with (event_set_prod_of_Z {[e]}); last first.
         { apply event_set_prod_of_Z_singleton. }
         assert ((event_set_prod_of_Z (event_set_Z_of_prod (event_set_prod_of_Z h ∪ event_set_prod_of_Z {[e]}))) =
                 (event_set_prod_of_Z h ∪ event_set_prod_of_Z {[e]})) as Hf1.
         { rewrite -event_set_prod_of_Z_union.
           by rewrite event_set_Z_of_prod_of_Z. }
         rewrite Hf1.
         iFrame.
         assert (event_set_prod_of_Z (event_set_Z_of_prod (event_set_prod_of_Z s1 ∪ event_set_prod_of_Z {[e]})) =
                (event_set_prod_of_Z s1 ∪ event_set_prod_of_Z {[e]})) as Hf2.
         { rewrite -event_set_prod_of_Z_union.
           by rewrite event_set_Z_of_prod_of_Z. }
         rewrite Hf2.
         rewrite - !event_set_prod_of_Z_union.
         rewrite! event_set_Z_of_prod_of_Z.
         rewrite! event_Z_of_prod_of_Z.
         simplify_eq /=.
         assert (EV_Op e = Add (Z.to_nat z)) as Hez.
         { destruct (EV_Op e) as (z0). f_equal.
           apply to_pn_op_inj. simplify_eq /=. rewrite He1. symmetry.
           destruct (bool_decide (0 ≤ Z.to_nat z)%Z) eqn:Hle; simplify_eq /=; eauto with lia.
           - apply bool_decide_eq_true in Hle.
             destruct z; simplify_eq /=; rewrite /pnop_left;
               apply prodOp_val_eq; simpl; f_equal.
             replace (Z.of_nat (Z.to_nat (Z.pos p))) with (Z.pos p) by lia.
             simpl. f_equal.
           - apply bool_decide_eq_false in Hle; lia. }
         iSplit.
         { iPureIntro. rewrite Hez. f_equal. eauto with lia. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro.
           intros x Hx.
           apply event_set_prod_of_Z_in in Hx.
           assert (event_prod_of_Z x ∈ s2p) as Hxs2p. { eapply elem_of_weaken; set_solver. }
           apply event_set_prod_of_Z_in_inv.
           by rewrite event_set_prod_of_Z_of_prod. }
         iSplit.
         { iPureIntro.
           intro Habs. apply He6.
           by apply event_set_prod_of_Z_in in Habs. }
         iSplit.
         { iPureIntro.
           intro Habs. apply He7.
           by apply event_set_prod_of_Z_in in Habs. }
         iSplit.
         { iPureIntro.
           apply event_set_prod_of_Z_in_inv.
           rewrite -event_set_prod_of_Z_singleton in He8.
           rewrite -event_set_prod_of_Z_union in He8.
           by rewrite -event_set_prod_of_Z_compute_maximals. }
         iSplit.
         { iPureIntro.
           by apply event_set_maximal_helper. }
         by rewrite event_set_prod_of_Z_of_prod.
    - wp_apply ("Hspec" $! (#0, #(-z))%V (pnop_right ((Z.to_nat (-z))))); try eauto.
      -- iPureIntro. simpl. rewrite /prodOp_coh /StLib_Op_Coh /= /gctr_op_coh /=.
         eexists #0, #(-z). split_and!; eauto.
         --- symmetry. f_equal. f_equal.
             assert (0 <= (- z))%Z by lia.
             unfold_prodOp_projs.
             apply Z2Nat.id. simplify_eq /=; eauto with lia.
      -- iMod "Hvsh".
         iDestruct "Hvsh" as (h s1 s2) "((HGst & HLst) & Hvsh)".
         iExists (event_set_prod_of_Z h),
                   (event_set_prod_of_Z s1),
                     (event_set_prod_of_Z s2).
         iFrame.
         iModIntro.
         iNext.
         iIntros (ep hp s1p s2p)
                 "(%He1 & %He2 & %He3 & %He4 & %He5 & %He6 & %He7 & %He8 & %He9 & HGst & HLst)".
         iDestruct (LocState_TakeSnap with "HLst") as "(HLst & #Hsnap)".
         iMod (LocSnap_Ext
                 _ repId repId s1p s2p
                with "[$][$][$]") as "%Hext";
           [solve_ndisj| ].
         iApply ("Hvsh" $!
                        (event_Z_of_prod ep)
                      (event_set_Z_of_prod hp)
                      (event_set_Z_of_prod s1p)
                      (event_set_Z_of_prod s2p)).
         simplify_eq /=.
         assert (∃ e, event_prod_of_Z e = ep) as Hf1.
         { exists {| EV_Op := Add z; EV_Orig := ep.(EV_Orig);  EV_Time := ep.(EV_Time) |}.
           rewrite /event_prod_of_Z. simplify_eq /=.
           destruct ep. f_equal /=.
           rewrite He1. simplify_eq /=.
           destruct (bool_decide (0 ≤ Z.to_nat (-z))%Z) eqn:Hle; simplify_eq /=; eauto with lia.
           - apply bool_decide_eq_true in Hle.
             destruct z; simplify_eq /=; rewrite /pnop_left;
                apply prodOp_val_eq; simpl; f_equal. lia.
           - apply bool_decide_eq_false in Hle; lia. }
         destruct Hf1 as (e & <-).
         replace ({[event_prod_of_Z e]}) with (event_set_prod_of_Z {[e]}); last first.
         { apply event_set_prod_of_Z_singleton. }
         assert ((event_set_prod_of_Z (event_set_Z_of_prod (event_set_prod_of_Z h ∪ event_set_prod_of_Z {[e]}))) =
                 (event_set_prod_of_Z h ∪ event_set_prod_of_Z {[e]})) as Hf1.
         { rewrite -event_set_prod_of_Z_union.
           by rewrite event_set_Z_of_prod_of_Z. }
         rewrite Hf1.
         iFrame.
         assert (event_set_prod_of_Z (event_set_Z_of_prod (event_set_prod_of_Z s1 ∪ event_set_prod_of_Z {[e]})) =
                (event_set_prod_of_Z s1 ∪ event_set_prod_of_Z {[e]})) as Hf2.
         { rewrite -event_set_prod_of_Z_union.
           by rewrite event_set_Z_of_prod_of_Z. }
         rewrite Hf2.
         rewrite - !event_set_prod_of_Z_union.
         rewrite! event_set_Z_of_prod_of_Z.
         rewrite! event_Z_of_prod_of_Z.
         simplify_eq /=.
         assert (EV_Op e = Add z) as Hez.
         { destruct (EV_Op e) as (z0). f_equal.
           apply to_pn_op_inj. simplify_eq /=. rewrite He1. symmetry.
           destruct (bool_decide (0 ≤ Z.to_nat z)%Z) eqn:Hle; simplify_eq /=; eauto with lia.
           - apply bool_decide_eq_true in Hle.
             destruct z; simplify_eq /=; rewrite /pnop_right;
               apply prodOp_val_eq; simpl; f_equal. lia.
           - apply bool_decide_eq_false in Hle; lia. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro. done. }
         iSplit.
         { iPureIntro.
           intros x Hx.
           apply event_set_prod_of_Z_in in Hx.
           assert (event_prod_of_Z x ∈ s2p) as Hxs2p. { eapply elem_of_weaken; set_solver. }
           apply event_set_prod_of_Z_in_inv.
           by rewrite event_set_prod_of_Z_of_prod. }
         iSplit.
         { iPureIntro.
           intro Habs. apply He6.
           by apply event_set_prod_of_Z_in in Habs. }
         iSplit.
         { iPureIntro.
           intro Habs. apply He7.
           by apply event_set_prod_of_Z_in in Habs. }
         iSplit.
         { iPureIntro.
           apply event_set_prod_of_Z_in_inv.
           rewrite -event_set_prod_of_Z_singleton in He8.
           rewrite -event_set_prod_of_Z_union in He8.
           by rewrite -event_set_prod_of_Z_compute_maximals. }
         iSplit.
         { iPureIntro.
           by apply event_set_maximal_helper. }
         by rewrite event_set_prod_of_Z_of_prod.
  Qed.


  (* TODO: Prove: *)
  (* Definition pncounter_init : val :=  *)
  (*   λ: "addrs" "rid", *)
  (*    let: "pn_cpt" := pn_cpt_init "addrs" "rid" in *)
  (*    let: "get_st" := Fst "pn_cpt" in *)
  (*    let: "upd_st" := Snd "pn_cpt" in *)
  (*    let: "get" := (λ: <>, pncounter_eval "get_st" #()) in *)
  (*    let: "upd" :=  (λ: "n", pncounter_update "upd_st" "n") in ("get", "upd"). *)

  Lemma pncounter_init_crdt_spec :
    GlobInv ⊢
    pn_prod_init_crdt_spec pn_cpt_init -∗
    pn_init_crdt_spec pncounter_init.
  Proof.
    rewrite /pn_prod_init_crdt_spec /pn_init_crdt_spec /init_spec_for_specific_crdt.
    iIntros "#Hinv #Hspec".
    iIntros (repId addr addrs_val Φ) "!#".
    iIntros "(%Hlst & %Hin & Hproto & Haddr & Hfps & Htk) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[$Hproto $Haddr $Htk $Hfps]"); try eauto.
    iIntros (gsv updv) "(HLst & #Hgspec & #Hupdspec)".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPoseProof (pncounter_eval_spec gsv repId addr with "Hinv Hgspec") as "Hs1".
    rewrite /pn_get_state_spec.
    iPoseProof (pncounter_update_spec updv repId addr with "Hinv Hupdspec") as "Hs2".
    iFrame "#".
  Qed.

End pncounter_proof.

(* Lemma elements_event_set_prod_of_Z (s : event_set CtrOp) :
    elements (event_set_prod_of_Z s) = event_prod_of_Z <$> elements s.
  Proof.
  Admitted.

  Lemma event_set_prod_of_Z_compute_maximum (s : event_set CtrOp) :
    maximality.compute_maximum (event_set_prod_of_Z s) =
      event_prod_of_Z <$> (maximality.compute_maximum s).
  Proof.
    rewrite /maximality.compute_maximum.
    destruct (elements (maximality.compute_maximals (event_set_prod_of_Z s))) as [ | f r] eqn:Hmax;
      destruct (elements (maximality.compute_maximals s)) as [ | f' r'] eqn:Hmax'.
    - done.
    - destruct r' as [ | r1 r2 ] eqn:Hmax''; [ | done].
      rewrite event_set_prod_of_Z_compute_maximals in Hmax.
      assert (maximality.compute_maximals s = ∅) as Hmaxeq.
      { apply elements_gset_empty_inv in Hmax.
        rewrite /event_set_prod_of_Z in Hmax.
        apply gset_map_empty_inv in Hmax.
        done. }
      rewrite Hmaxeq in Hmax'.
      inversion Hmax'.
    - destruct r as [ | r1 r2 ] eqn:Hmax''; [ | done].
      rewrite event_set_prod_of_Z_compute_maximals in Hmax.
      assert (maximality.compute_maximals s = ∅) as Hmaxeq.
      { apply elements_gset_empty_inv in Hmax'. done. }
      rewrite Hmaxeq in Hmax.
      inversion Hmax.
    - destruct r as [ | r1 r2] eqn:Hmax''.
      + destruct r' as [ | r1' r2'] eqn:Hmax'''.
        * simpl.
          rewrite event_set_prod_of_Z_compute_maximals in Hmax.
          rewrite maximality.set_singleton_elements in Hmax.
          rewrite maximality.set_singleton_elements in Hmax'.
          rewrite Hmax' in Hmax.
          rewrite event_set_prod_of_Z_singleton in Hmax.
          f_equal.
          apply gset_singleton_eq_elem in Hmax.
          done.
        * simpl in *.
          rewrite event_set_prod_of_Z_compute_maximals in Hmax.
          exfalso.
          rewrite elements_event_set_prod_of_Z in Hmax.
          rewrite Hmax' in Hmax.
          simpl in Hmax.
          inversion Hmax.
      + destruct r' as [ | r1' r2' ] eqn:Hmax'''.
        *  rewrite event_set_prod_of_Z_compute_maximals in Hmax.
           exfalso.
           rewrite elements_event_set_prod_of_Z in Hmax.
           rewrite Hmax' in Hmax.
           simpl in Hmax.
           inversion Hmax.
        * done.
  Qed.

  Lemma event_set_Z_of_prod_compute_maximum (s : event_set pn_prod_Op) :
    maximality.compute_maximum (event_set_Z_of_prod s) = event_Z_of_prod <$> (maximality.compute_maximum s).
  Proof.
  Admitted. *)

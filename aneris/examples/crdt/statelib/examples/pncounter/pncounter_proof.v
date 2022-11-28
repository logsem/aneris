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
  Context `{!anerisG M Σ, !CRDT_Params, !StLib_Res (prodOp gctr_op gctr_op)}.

  Notation pnOp := (prodOp gctr_op gctr_op).
  Notation pnSt := (prodSt gctr_st gctr_st).
  Notation pnParams := (prod_params gctr_op gctr_st gctr_op gctr_st).

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
       exists ((list_sum lacc + n)). split; eauto with lia.
       rewrite list_sum_app. simpl. eauto with lia.
    - iPureIntro. simpl. split_and!; try eauto. exists 0; done.
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

  Notation pn_prod_Op := (prodOp gctr_op gctr_op).

  Definition event_prod_of_Z (ev : Event CtrOp) : Event pn_prod_Op :=
    let z := ctr_payload ev.(EV_Op) in
    let op := if bool_decide (Z.le 0 z) then (Z.to_nat z, 0) else (0, Z.to_nat (-z)) in
   {| EV_Op := op ;  EV_Orig := ev.(EV_Orig);  EV_Time := ev.(EV_Time) |}.

  Definition event_set_prod_of_Z (s : event_set CtrOp) : event_set pn_prod_Op :=
    gset_map (λ ev, event_prod_of_Z ev) s.

  Definition event_Z_of_prod (ev : Event pn_prod_Op) : Event CtrOp :=
    let (p,n) := ev.(EV_Op) in
    {| EV_Op := Add (p-n);  EV_Orig := ev.(EV_Orig);  EV_Time := ev.(EV_Time) |}.

  Definition event_set_Z_of_prod (s : event_set pn_prod_Op) : event_set CtrOp :=
    gset_map (λ ev, event_Z_of_prod ev) s.

End pn_event_mapping.

Section pn_Res_mapping.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op)}.

  Global Program Instance pn_Res : StLib_Res CtrOp :=
    {|
      StLib_InitToken := pn_prod_Res.(StLib_InitToken);
      StLib_SocketProto := pn_prod_Res.(StLib_SocketProto);
    |}.
  Next Obligation.
  Admitted.

End pn_Res_mapping.

Section pn_prod_specs_def.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op)}.

  Notation pn_prod_Op := (prodOp gctr_op gctr_op).
  Notation pn_prod_St := (prodSt gctr_st gctr_st).
  Notation pn_prod_Params := (prod_params gctr_op gctr_st gctr_op gctr_st).

  Definition pn_prod_upd_spec := (@update_spec pn_prod_Op pn_prod_St _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res).
  Definition pn_prod_get_state_spec := (@get_state_spec pn_prod_Op pn_prod_St _ _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res).
  Definition pn_prod_init_crdt_spec :=
    @init_spec_for_specific_crdt pn_prod_Op pn_prod_St _ _ _ _ _ _ _ (prod_crdt_coh_params _ _ _ _) pn_prod_Res.

End pn_prod_specs_def.

Section pn_specs_def.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_Res : !StLib_Res CtrOp}.

  Definition pn_get_state_spec := (@get_state_spec CtrOp CtrSt _ _ _ _ _ _ _ Ctr_Coh_Params pn_Res).
  Definition pn_upd_spec := @update_spec CtrOp CtrSt _ _ _ _ _ _ Ctr_Coh_Params pn_Res.
  Definition pn_init_crdt_spec :=
    @init_spec_for_specific_crdt CtrOp CtrSt _ _ _ _ _ _ _ Ctr_Coh_Params pn_Res.

End pn_specs_def.

Section pncounter_proof.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{pn_prod_Res : !StLib_Res (prodOp gctr_op gctr_op)}.

  (* TODO: Prove: *)
  (* Definition pncounter_update : val := *)
  (*   λ: "upd" "n", *)
  (*     (if: #0 ≤ "n" *)
  (*      then  "upd" ("n", #0) *)
  (*      else  "upd" (#0, (- "n"))). *)
  Lemma pncounter_update_spec (upd_fn : val) repId addr:
    pn_prod_upd_spec upd_fn repId addr -∗
    pn_upd_spec (λ:"n", pncounter_update upd_fn "n") repId addr.
  Proof. Admitted.


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
    pn_prod_get_state_spec get_state_fn repId addr -∗
    pn_get_state_spec (λ:<>, pncounter_update get_state_fn #()) repId addr.
  Proof. Admitted.

  (* TODO: Prove: *)
  (* Definition pncounter_init : val := *)
  (*   λ: "addrs" "rid", *)
  (*     let: "pn_cpt" := pn_cpt_init "addrs" "rid" in *)
  (*     let: "get_st" := Fst "pn_cpt" in *)
  (*     let: "upd_st" := Snd "pn_cpt" in *)
  (*     let: "get" := pncounter_eval "get_st" in *)
  (*     let: "upd" := pncounter_update "upd_st" in *)
  (*     ("get", "upd"). *)
  Lemma pncounter_init_crdt_spec :
    pn_prod_init_crdt_spec pn_cpt_init -∗
    pn_init_crdt_spec pncounter_init.
  Proof. Admitted.

End pncounter_proof.

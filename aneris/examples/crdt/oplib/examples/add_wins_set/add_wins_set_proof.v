From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.add_wins_set Require Import add_wins_set_code.

Section awsCrdt.
  Context `{!Log_Time} `{!EqDecision vl} `{!Countable vl}.

  Inductive awsOp : Type :=
  | Add : vl → awsOp
  | Remove : vl → awsOp.

  Definition awsSt : Type := gset (vl * Time).

  Global Instance awsOp_eqdec : EqDecision awsOp.
  Proof. solve_decision. Qed.

  Global Instance awsOp_countable : Countable awsOp.
  Proof.
    apply (inj_countable'
             (λ op, match op with Add v => inl v | Remove v => inr v end)
             (λ x, match x with inl v => Add v | inr v => Remove v end));
    intros []; done.
  Qed.

  Definition aws_denot (s : gset (Event awsOp)) (state : awsSt) : Prop :=
    ∀ v tm,
      (v, tm) ∈ state ↔
      ∃ add_ev, add_ev ∈ s ∧ EV_Op add_ev = Add v ∧ EV_Time add_ev = tm ∧
        ∀ rm_ev, rm_ev ∈ s → EV_Op rm_ev = Remove v → ¬ TM_le tm (EV_Time rm_ev).

  Global Instance aws_denot_fun : Rel2__Fun aws_denot.
  Proof.
    constructor; intros s st1 st2 Hst1 Hst2.
    apply set_eq; intros [v tm].
    rewrite Hst1 Hst2; done.
  Qed.

  Global Instance aws_denot_instance : CrdtDenot awsOp awsSt := {
    crdt_denot := aws_denot;
  }.
End awsCrdt.

Global Arguments awsOp _ : clear implicits.
Global Arguments awsSt {_} _ {_ _}.

(* TODO: Move to the right place. *)
Global Instance TM_le_dec `{!Log_Time} tm1 tm2 : Decision (TM_le tm1 tm2).
Proof.
  destruct (decide (TM_lt tm1 tm2)).
  { left; apply TM_lt_TM_le; done. }
  destruct (decide (tm1 = tm2)) as [->|].
  { left; reflexivity. }
  right; intros []%TM_le_eq_or_lt; done.
Qed.

Section OpAws.
  Context `{!Log_Time}
          `{!EqDecision vl} `{!Countable vl}.

  Definition update_state (ev : Event (awsOp vl)) (st : awsSt vl) : awsSt vl :=
    match EV_Op ev with
    | Add v => {[(v, EV_Time ev)]} ∪ st
    | Remove v =>  filter (λ '(w, tm), v ≠ w ∨ ¬ TM_le tm (EV_Time ev)) st
    end.

  Definition op_aws_effect (st : awsSt vl) (ev : Event (awsOp vl)) (st' : awsSt vl) : Prop :=
    st' = update_state ev st.

  Lemma op_aws_effect_fun st : Rel2__Fun (op_aws_effect st).
  Proof. constructor; intros ??? -> ->; done. Qed.

  Instance op_aws_effect_coh : OpCrdtEffectCoh op_aws_effect.
  Proof.
    intros s ev st st' Hst Hevs Hmax Hext Hto.
    rewrite /op_aws_effect /crdt_denot /= /aws_denot /update_state.
    split.
    - intros ->.
      intros v tm; split.
      + intros Hup.
        destruct ev as [[add_vl|rm_vl] evorig evtm]; simpl in *.
        * rewrite elem_of_union elem_of_singleton in Hup.
          destruct Hup as [|Hup]; simplify_eq.
          -- exists {| EV_Op := Add add_vl; EV_Orig := evorig; EV_Time := evtm |}; simpl.
             split_and!; [set_solver|done|done|].
             intros [[|rm_val] rm_orig rm_tm] Hrmvs ?; simpl in *; first done.
             destruct Hmax as [? Hmax].
             specialize (Hmax _ Hrmvs).
             rewrite /time /= in Hmax.
             intros [->|Hle]%TM_le_eq_or_lt; last done.
             simplify_eq.
             assert ({| EV_Op := Add add_vl; EV_Orig := evorig; EV_Time := rm_tm |} =
                       {| EV_Op := Remove add_vl; EV_Orig := rm_orig; EV_Time := rm_tm |});
                  last by simplify_eq.
             apply Hext; set_solver.
          -- apply Hst in Hup as (add_ev&?&?&?&?).
             exists add_ev; split_and!; [set_solver|done|done|set_solver].
        * apply elem_of_filter in Hup as [Hupin Hup].
          apply Hst in Hup as (add_ev&?&?&?&Hno_rm); simplify_eq.
          exists add_ev; split_and!; [set_solver|done|done|].
          intros rm_ev Hrm_ev ?.
          pose proof Hrm_ev as Hrm_ev'.
          rewrite elem_of_union elem_of_singleton in Hrm_ev'.
          destruct Hrm_ev' as [|]; first by apply Hno_rm.
          simplify_eq/=; simpl.
          destruct Hupin; done.
      + intros (add_ev & Hadd_ev_in & Hadd_ev_val & Hadd_ev_tm & Hadd_ev_no_rm).
        destruct ev as [[add_vl|rm_vl] evorig evtm]; simpl in *.
        * rewrite elem_of_union elem_of_singleton in Hadd_ev_in.
          destruct Hadd_ev_in as [Hadd_ev_in|]; simplify_eq/=; last set_solver.
          apply elem_of_union; right.
          apply Hst.
          exists add_ev; split_and!; [done|done|done|set_solver].
        * apply elem_of_filter.
          split.
          -- destruct (decide (rm_vl = v)); last tauto.
             right;
               apply (Hadd_ev_no_rm {| EV_Op := Remove rm_vl; EV_Orig := evorig; EV_Time := evtm |});
               [set_solver|simpl; congruence].
          -- apply Hst; exists add_ev; split_and!; [set_solver|done|done|set_solver].
    - intros Hst'.
      apply set_eq; intros [v tm]; split.
      + intros (add_ev & Hadd_ev_in & Hadd_ev_val & Hadd_ev_tm & Hadd_ev_no_rm)%Hst'.
        destruct ev as [[add_vl|rm_vl] evorig evtm]; simpl in *.
        * rewrite elem_of_union elem_of_singleton in Hadd_ev_in.
          destruct Hadd_ev_in as [Hadd_ev_in|]; simplify_eq/=; last set_solver.
          apply elem_of_union; right.
          apply Hst.
          exists add_ev; split_and!; [done|done|done|set_solver].
        * apply elem_of_filter.
          split.
          -- destruct (decide (rm_vl = v)); last tauto.
             right;
               apply (Hadd_ev_no_rm {| EV_Op := Remove rm_vl; EV_Orig := evorig; EV_Time := evtm |});
               [set_solver|simpl; congruence].
          -- apply Hst; exists add_ev; split_and!; [set_solver|done|done|set_solver].
      + intros Hup.
        destruct ev as [[add_vl|rm_vl] evorig evtm]; simpl in *.
        * rewrite elem_of_union elem_of_singleton in Hup.
          destruct Hup as [|Hup]; simplify_eq.
          -- apply Hst'.
             exists {| EV_Op := Add add_vl; EV_Orig := evorig; EV_Time := evtm |}; simpl.
             split_and!; [set_solver|done|done|].
             intros [[|rm_val] rm_orig rm_tm] Hrmvs ?; simpl in *; first done.
             destruct Hmax as [? Hmax].
             specialize (Hmax _ Hrmvs).
             rewrite /time /= in Hmax.
             intros [->|Hle]%TM_le_eq_or_lt; last done.
             simplify_eq.
             assert ({| EV_Op := Add add_vl; EV_Orig := evorig; EV_Time := rm_tm |} =
                       {| EV_Op := Remove add_vl; EV_Orig := rm_orig; EV_Time := rm_tm |});
                  last by simplify_eq.
             apply Hext; set_solver.
          -- apply Hst'.
             apply Hst in Hup as (add_ev&?&?&?&?).
             exists add_ev; split_and!; [set_solver|done|done|set_solver].
        * apply Hst'.
          apply elem_of_filter in Hup as [Hupin Hup].
          apply Hst in Hup as (add_ev&?&?&?&Hno_rm); simplify_eq.
          exists add_ev; split_and!; [set_solver|done|done|].
          intros rm_ev Hrm_ev ?.
          pose proof Hrm_ev as Hrm_ev'.
          rewrite elem_of_union elem_of_singleton in Hrm_ev'.
          destruct Hrm_ev' as [|]; first by apply Hno_rm.
          simplify_eq/=; simpl.
          destruct Hupin; done.
  Qed.

  Definition op_aws_init_st : awsSt vl := ∅.

  Lemma op_aws_init_st_coh : ⟦ (∅ : gset (Event (awsOp vl))) ⟧ ⇝ op_aws_init_st.
  Proof.
    intros ? ?; split; first set_solver.
    intros (?&?&?); set_solver.
  Qed.

  Global Instance op_aws_model_instance : OpCrdtModel (awsOp vl) (awsSt vl) := {
    op_crdtM_effect := op_aws_effect;
    op_crdtM_effect_fun := op_aws_effect_fun;
    op_crdtM_effect_coh := op_aws_effect_coh;
    op_crdtM_init_st := op_aws_init_st;
    op_crdtM_init_st_coh := op_aws_init_st_coh
  }.

End OpAws.

From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_code list_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.crdt.oplib.proof Require Import time.

(* TODO: move to the right place. *)
Global Instance vector_clock_inject : Inject vector_clock val :=
  { inject := vector_clock_to_val }.

Section aws_proof.
  Context `{!EqDecision vl} `{!Countable vl}
          `{!Inject vl val} `{!∀ (a : vl), Serializable vl_serialization $a}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params} `{!OpLib_Res (awsOp vl)}.

  Global Program Instance awsOp_inj : Inject (awsOp vl) val :=
    {| inject w := match w with add_wins_set_proof.Add v => InjLV $v | Remove v => InjRV $v end |}.
  Next Obligation.
  Proof. intros [] []; simpl; intros ?; simplify_eq; done. Qed.
  
  Definition aws_OpLib_Op_Coh := λ (op : awsOp vl) (v : val), v = $op.

  Lemma aws_OpLib_Op_Coh_Inj (o1 o2 : awsOp vl) (v : val) :
    aws_OpLib_Op_Coh o1 v → aws_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. rewrite /aws_OpLib_Op_Coh; intros ? ?; simplify_eq; done. Qed.

  Lemma aws_OpLib_Coh_Ser (op : awsOp vl) (v : val) :
    aws_OpLib_Op_Coh op v → Serializable (sum_serialization vl_serialization vl_serialization) v.
  Proof. intros Heq. rewrite Heq; destruct op; apply _. Qed.

  Definition aws_OpLib_State_Coh :=
    λ (st : awsSt vl) v, ∃ (l : list (vl * vector_clock)), is_list l v ∧ ∀ vtm, vtm ∈ st ↔ vtm ∈ l.

  Global Instance aws_OpLib_Params : OpLib_Params (awsOp vl) (awsSt vl) :=
  {|
    OpLib_Serialization := (sum_serialization vl_serialization vl_serialization);
    OpLib_State_Coh := aws_OpLib_State_Coh;
    OpLib_Op_Coh := aws_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := aws_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := aws_OpLib_Coh_Ser
  |}.

  Lemma aws_init_st_fn_spec : ⊢ init_st_fn_spec init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    iApply "HΦ".
    iPureIntro; eexists []; split_and!; [done|set_solver].
  Qed.

  (* TODO: moe to the right place; this strengthenes the existing proof. *)
  (* This also changes the API to use filter instead of list.filter. Why whas that choice made!?*)
  Lemma wp_list_filter `{!Inject A val} (l : list A) (P : A -> bool) (f lv : val) ip :
    {{{ (∀ (x : A),
            {{{ ⌜x ∈ l⌝ }}}
              f $x @[ip]
            {{{ w, RET w; ⌜w = $(P x)⌝ }}} ) ∗
        ⌜is_list l lv⌝ }}}
       list_code.list_filter f lv @[ip]
     {{{ rv, RET rv; ⌜is_list (filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_code.list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_code.list_filter.
      do 7 (wp_pure _).
      fold list_code.list_filter.
      wp_apply ("IH" $! lv'); [done| |].
      { iIntros "!#" (? ?) "!# %"; iApply "Hf"; iPureIntro; apply elem_of_cons; auto. }
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [by iPureIntro; apply elem_of_cons; auto|].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply wp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        rewrite filter_cons.
        rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        rewrite filter_cons.
        rewrite HP. done.
  Qed.

  Lemma aws_effect_spec : ⊢ effect_spec effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect.
    destruct log_ev as [log_ev orig vc].
    destruct Hev as (evpl&evvc&evorig& ?&Hopcoh&?&?).
    destruct Hevs as (Hnin & Hmax & Hext).
    destruct Hst as (l&?&Hstl).
    simplify_eq/=.
    rewrite Hopcoh /=.
    wp_pures.
    destruct log_ev; wp_pures.
    - replace ($ v, evvc)%V with ($ (v, vc) : val); last first.
      { simpl; erewrite is_vc_vector_clock_to_val; done. }
      wp_apply wp_list_cons; first by iPureIntro.
      iIntros (w Hw).
      iApply "HΦ".
      iExists _; iSplit; last by eauto.
      simpl; iPureIntro; eexists _; split_and!; first done.
      intros []; rewrite /update_state /=; set_solver.
    - wp_apply
        (wp_list_filter
           _ (λ '(w, wvc), (bool_decide (w ≠ v)) || (negb (bool_decide (vector_clock_le wvc vc))))).
      + iSplit; last done.
        iIntros ([w wvc]) "!#".
        iIntros (Ψ) "_ HΨ".
        wp_pures.
        destruct (decide (w = v)) as [->|Hneq].
        * wp_op; [rewrite bin_op_eval_eq_val bool_decide_eq_true_2; done|].
          wp_pures.
          wp_apply wp_vect_leq; first by iPureIntro; split; [apply vector_clock_to_val_is_vc|done].
          iIntros (? ->); simpl.
          wp_pures.
          iApply "HΨ".
          rewrite (bool_decide_eq_false_2 (v ≠ v)); by auto.
        * wp_op.
          { rewrite bin_op_eval_eq_val bool_decide_eq_false_2; first done.
            intros ?; apply Hneq; eapply inj; eauto with typeclass_instances. }
          wp_pures.
          iApply "HΨ".
          rewrite (bool_decide_eq_true_2 (w ≠ v)); by auto.
      + iIntros (w Hw).
        iApply "HΦ".
        iExists _; iSplit; last by eauto.
        simpl; iPureIntro; eexists _; split_and!; first done.
        intros [u uvc].
        rewrite /update_state /=.
        rewrite elem_of_filter elem_of_list_filter Hstl.
        rewrite -bool_decide_not -bool_decide_or bool_decide_spec.
        clear; firstorder.
  Qed.

  Lemma aws_crdt_fun_spec : ⊢ crdt_fun_spec aws_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /aws_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply aws_init_st_fn_spec; done.
    - iApply aws_effect_spec; done.
  Qed.

  Lemma aws_init_spec :
    init_spec
      (oplib_init
         (s_ser (s_serializer (sum_serialization vl_serialization vl_serialization)))
         (s_deser (s_serializer (sum_serialization vl_serialization vl_serialization)))) -∗
      init_spec_for_specific_crdt
        (aws_init (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr fixedAddrs addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /aws_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
    { do 3 (iSplit; first done). iApply aws_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End aws_proof.

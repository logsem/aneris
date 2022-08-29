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
From aneris.examples.crdt.oplib.examples.remove_wins_set Require Import remove_wins_set_code.

Section rwsCrdt.
  Context `{!Log_Time} `{!EqDecision vl} `{!Countable vl}.

  Inductive rwsOp : Type :=
  | Add : vl → rwsOp
  | Remove : vl → rwsOp.

  Record rwsSt : Type := { contents : gset (vl * Time); removes : gset (vl * Time) }.

  Global Instance rwsOp_eqdec : EqDecision rwsOp.
  Proof. solve_decision. Qed.

  Global Instance rwsOp_countable : Countable rwsOp.
  Proof.
    apply (inj_countable'
             (λ op, match op with Add v => inl v | Remove v => inr v end)
             (λ x, match x with inl v => Add v | inr v => Remove v end));
    intros []; done.
  Qed.

  Definition rws_denot (s : gset (Event rwsOp)) (state : rwsSt) : Prop :=
    (∀ v tm,
      (v, tm) ∈ contents state ↔
      ∃ add_ev, add_ev ∈ s ∧ EV_Op add_ev = Add v ∧ EV_Time add_ev = tm ∧
        ∀ rm_ev, rm_ev ∈ s → EV_Op rm_ev = Remove v → TM_lt (EV_Time rm_ev) tm) ∧
    (∀ v tm,
      (v, tm) ∈ removes state ↔
      ∃ rem_ev, rem_ev ∈ s ∧ EV_Op rem_ev = Remove v ∧ EV_Time rem_ev = tm).

  Global Instance rws_denot_fun : Rel2__Fun rws_denot.
  Proof.
    constructor; intros s [cnts1 rms1] [cnts2 rms2] [Hst1cnts Hst1rms] [Hst2cnts Hst2rms].
    f_equal.
    - apply set_eq; intros [v tm].
      rewrite Hst1cnts Hst2cnts; done.
    - apply set_eq; intros [v tm].
      rewrite Hst1rms Hst2rms; done.
  Qed.

  Global Instance rws_denot_instance : CrdtDenot rwsOp rwsSt := {
    crdt_denot := rws_denot;
  }.
End rwsCrdt.

Global Arguments rwsOp _ : clear implicits.
Global Arguments rwsSt {_} _ {_ _}.

(* TODO: Move to the right place. *)
Global Instance TM_le_dec `{!Log_Time} tm1 tm2 : Decision (TM_le tm1 tm2).
Proof.
  destruct (decide (TM_lt tm1 tm2)).
  { left; apply TM_lt_TM_le; done. }
  destruct (decide (tm1 = tm2)) as [->|].
  { left; reflexivity. }
  right; intros []%TM_le_eq_or_lt; done.
Qed.

(* TODO: is this a bug? Why is this not declared an instance in stdpp? for performance reasons!? *)
Local Existing Instance list_exist_dec.

Section OpRws.
  Context `{!Log_Time}
          `{!EqDecision vl} `{!Countable vl}.

  Definition update_state (ev : Event (rwsOp vl)) (st : rwsSt vl) : rwsSt vl :=
    match EV_Op ev with
    | Add v =>
        {| contents := if bool_decide
                            (∃ r, r ∈ elements (removes st) ∧ r.1 = v ∧ ¬ TM_lt r.2 (EV_Time ev))
                       then contents st
                       else {[(v, EV_Time ev)]} ∪ contents st;
           removes := removes st |}
    | Remove v =>
        {| contents := filter (λ '(w, tm), v ≠ w ∨ TM_le (EV_Time ev) tm) (contents st);
           removes := {[(v, EV_Time ev)]} ∪ removes st |}
    end.

  Definition op_rws_effect (st : rwsSt vl) (ev : Event (rwsOp vl)) (st' : rwsSt vl) : Prop :=
    st' = update_state ev st.

  Lemma op_rws_effect_fun st : Rel2__Fun (op_rws_effect st).
  Proof. constructor; intros ??? -> ->; done. Qed.

  Instance op_rws_effect_coh : OpCrdtEffectCoh op_rws_effect.
  Proof.
    intros s ev [cnts rms] [cnts' rms'] [Hcnts Hrms] Hevs Hmax Hext Hto.
    rewrite /op_rws_effect /crdt_denot /= /rws_denot /update_state.
    split.
    - intros ->; split.
      + intros v tm; split.
        * intros Hup.
          destruct ev as [[add_vl|rm_vl] evorig evtm]; simpl in *.
          -- destruct (decide (∃ r, r ∈ elements rms ∧ r.1 = add_vl ∧ ¬ TM_lt r.2 evtm))
               as [([r_w r_tm] & Hrel & Hrval & Hrlt)|Hnor].
             ++ simplify_eq.
                rewrite bool_decide_eq_true_2 in Hup; last by eauto.
                apply Hcnts in Hup as (?&?&?&?&?); set_solver.
            ++ rewrite bool_decide_eq_false_2 in Hup; last done.
               rewrite elem_of_union elem_of_singleton in Hup.
               destruct Hup as [Hup|Hup]; last first.
               { apply Hcnts in Hup as (?&?&?&?&?); set_solver. }
               simplify_eq.
               exists ({|EV_Op := Add add_vl; EV_Orig := evorig; EV_Time := evtm|});
                 split_and!; [clear; set_solver|done|done|].
               intros [rm_vl rm_orig rm_tm] ? ?; simplify_eq/=.
               destruct (decide (TM_lt rm_tm evtm)); first done.
               exfalso; apply Hnor.
               exists (add_vl, rm_tm); split_and!; [|done|done].
               apply elem_of_elements.
               apply Hrms.
               exists ({|EV_Op := Remove add_vl; EV_Orig := rm_orig; EV_Time := rm_tm|}).
               split_and!; [set_solver|done|done].
          -- apply elem_of_filter in Hup as [Hup1 Hup2].
             apply Hcnts in Hup2 as (add_ev&?&?&?&?).
             exists add_ev; split_and!; [set_solver|done|done|].
             intros rm_ev.
             rewrite elem_of_union elem_of_singleton.
             intros [| ->]; first by auto with set_solver.
             intros ?; simplify_eq/=.
             destruct Hup1 as [|Hup1]; first done.
             apply TM_le_eq_or_lt in Hup1 as [Hup1|]; last done.
             assert ({| EV_Op := Remove v; EV_Orig := evorig; EV_Time := evtm |} = add_ev) as <-;
               last set_solver.
             apply Hext; [set_solver|set_solver|done].
        * intros (add_ev & Hadd_ev_in & Hadd_ev_val & Hadd_ev_tm & Hadd_ev_norem).
          rewrite elem_of_union elem_of_singleton in Hadd_ev_in.
          destruct Hadd_ev_in as [Hadd_ev_in| <-]; simpl in *.
          -- assert ((v, tm) ∈ cnts).
             { apply Hcnts; exists add_ev; split_and!; [done|done|done| set_solver]. }
             destruct ev as [[|w] w_orig w_tm] eqn:Heveq; simpl.
             ++ destruct bool_decide; set_solver.
             ++ apply elem_of_filter; split; last done.
                destruct (decide (v = w)) as [->|]; last by eauto.
                right.
                apply TM_lt_TM_le.
                apply (Hadd_ev_norem {| EV_Op := Remove w; EV_Orig := w_orig; EV_Time := w_tm |});
                  [set_solver|done].
          -- destruct add_ev as [[|w] w_orig w_tm] eqn:Heveq; [simplify_eq/=|by simplify_eq/=].
             destruct (decide (∃ r, r ∈ elements rms ∧ r.1 = v ∧ ¬ TM_lt r.2 tm))
               as [([w w_tm] & Hw_elem & Hw_val & Hw_lt)|Hnorm]; simplify_eq/=.
             ++ exfalso; apply Hw_lt.
                apply elem_of_elements in Hw_elem.
                apply Hrms in Hw_elem as (rm_ev&?&?&<-).
                apply (Hadd_ev_norem rm_ev); [set_solver|done].
             ++ rewrite bool_decide_eq_false_2; [set_solver|done].
      + simpl in *.
        destruct ev as [[w|w] w_orig w_tm]; simpl.
        * setoid_rewrite Hrms; clear; set_solver.
        * split.
          -- rewrite elem_of_union elem_of_singleton; intros [|]; [simplify_eq|set_solver].
             exists {| EV_Op := Remove w; EV_Orig := w_orig; EV_Time := w_tm |};
               split_and!; [set_solver|done|done].
          -- setoid_rewrite elem_of_union; setoid_rewrite elem_of_singleton.
            intros (?&[| ->]&?&?); last by simplify_eq/=; eauto.
            right; apply Hrms; eauto.
    - intros [Hcnts' Hrms']. simpl in *.
      destruct ev as [[|w] w_orig w_tm] eqn:Heveq; simpl.
      + f_equal; last first.
        { apply set_eq; intros []; rewrite Hrms Hrms'; clear; set_solver. }
        apply set_eq; intros (u, u_tm).
        split.
        * intros Hu.
          apply Hcnts' in Hu as (add_ev & Hadd_ev_s & Hadd_ev_val & Hadd_ev_tm & Hadd_ev_norem).
          rewrite elem_of_union elem_of_singleton in Hadd_ev_s.
          destruct Hadd_ev_s as [Hadd_ev_s|Hadd_ev_s].
          { assert ((u, u_tm) ∈ cnts); last by destruct bool_decide; set_solver.
            apply Hcnts; exists add_ev; split_and!; [done|done|done|set_solver]. }
          simplify_eq/=.
          rewrite bool_decide_eq_false_2; first set_solver.
          intros ([z z_tm] & Hz_in & ? & Hz_tm); simplify_eq/=.
          rewrite elem_of_elements in Hz_in.
          apply Hrms in Hz_in as (rm_ev&?&?&Hrem_ev_tm).
          exfalso; apply Hz_tm.
          specialize (Hadd_ev_norem rm_ev).
          rewrite Hrem_ev_tm in Hadd_ev_norem.
          apply Hadd_ev_norem; [set_solver|done].
        * destruct (decide (∃ r, r ∈ elements rms ∧ r.1 = v ∧ ¬ TM_lt r.2 w_tm))
            as [(rm_ev & Hrm_ev_in & Hrm_ev_val & Hrm_ev_tm)|Hnorm].
          -- rewrite bool_decide_eq_true_2; last by eauto.
             rewrite Hcnts Hcnts'; clear; set_solver.
          -- rewrite bool_decide_eq_false_2; last done.
             rewrite elem_of_union elem_of_singleton; intros [|Hincnt].
             ++ simplify_eq.
                apply Hcnts'.
                exists {| EV_Op := Add v; EV_Orig := w_orig; EV_Time := w_tm |};
                  split_and!; [set_solver|done|done|].
                intros ? ? ?.
                destruct (decide (TM_lt (EV_Time rm_ev) w_tm)) as [|Hnlt]; first done.
                exfalso; apply Hnorm.
                set_solver.
             ++ revert Hincnt. rewrite Hcnts Hcnts'; clear; set_solver.
      + f_equal; last first.
        { apply set_eq; intros []; rewrite elem_of_union Hrms Hrms'; clear.
          setoid_rewrite elem_of_union. setoid_rewrite elem_of_singleton.
          split.
          - intros ([]&[|]&?&?); simplify_eq/=; set_solver.
          - intros [|([]&?&?&?)]; first simplify_eq/=.
            + eexists; split_and!; [right; reflexivity|done|done].
            + eexists; split_and!; [by left|done|done]. }
        apply set_eq; intros (u, u_tm).
        rewrite elem_of_filter.
        rewrite Hcnts' Hcnts.
        split.
        * intros ([z z_orig z_tm]&Hz_in&z_val&z_tm_eq&z_norm).
          rewrite elem_of_union elem_of_singleton in Hz_in.
          destruct Hz_in as [Hz_in|?]; [simplify_eq/=|by simplify_eq/=].
          split; last set_solver.
          destruct (decide (w = u)) as [->|]; last tauto.
          right.
          apply TM_lt_TM_le.
          apply (z_norm {| EV_Op := Remove u; EV_Orig := w_orig; EV_Time := w_tm |});
            [clear; set_solver|done].
        * intros [Hneqle ([z z_orig z_tm]&Hz_in&z_val&z_tm_eq&z_norm)];
            simplify_eq/=.
          exists {| EV_Op := Add u; EV_Orig := z_orig; EV_Time := u_tm |};
          split_and!; [set_solver|done|done|].
          intros rm_ev Hrm_ev_in.
          rewrite elem_of_union elem_of_singleton in Hrm_ev_in.
          destruct Hrm_ev_in as [Hrm_ev_in|]; simplify_eq; first by apply z_norm.
          intros ?; simplify_eq/=.
          destruct Hneqle as [|Hle]; first done.
          apply TM_le_eq_or_lt in Hle as [|]; last done.
          simplify_eq.
          assert ({| EV_Op := Add u; EV_Orig := z_orig; EV_Time := u_tm |} =
                  {| EV_Op := Remove u; EV_Orig := w_orig; EV_Time := u_tm |});
            last done.
          apply Hext; [set_solver|set_solver|done].
  Qed.

  Definition op_rws_init_st : rwsSt vl := {| contents := ∅; removes := ∅ |}.

  Lemma op_rws_init_st_coh : ⟦ (∅ : gset (Event (rwsOp vl))) ⟧ ⇝ op_rws_init_st.
  Proof. split; set_solver. Qed.

  Global Instance op_rws_model_instance : OpCrdtModel (rwsOp vl) (rwsSt vl) := {
    op_crdtM_effect := op_rws_effect;
    op_crdtM_effect_fun := op_rws_effect_fun;
    op_crdtM_effect_coh := op_rws_effect_coh;
    op_crdtM_init_st := op_rws_init_st;
    op_crdtM_init_st_coh := op_rws_init_st_coh
  }.

End OpRws.

From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_code list_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.crdt.oplib.proof Require Import time.

(* TODO: move to the right place. *)
Global Instance vector_clock_inject : Inject vector_clock val :=
  { inject := vector_clock_to_val }.

Section rws_proof.
  Context `{!EqDecision vl} `{!Countable vl}
          `{!Inject vl val} `{!∀ (a : vl), Serializable vl_serialization $a}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params} `{!OpLib_Res (rwsOp vl)}.

  Global Program Instance rwsOp_inj : Inject (rwsOp vl) val :=
    {| inject w := match w with remove_wins_set_proof.Add v => InjLV $v | Remove v => InjRV $v end |}.
  Next Obligation.
  Proof. intros [] []; simpl; intros ?; simplify_eq; done. Qed.

  Definition rws_OpLib_Op_Coh := λ (op : rwsOp vl) (v : val), v = $op.

  Lemma rws_OpLib_Op_Coh_Inj (o1 o2 : rwsOp vl) (v : val) :
    rws_OpLib_Op_Coh o1 v → rws_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. rewrite /rws_OpLib_Op_Coh; intros ? ?; simplify_eq; done. Qed.

  Lemma rws_OpLib_Coh_Ser (op : rwsOp vl) (v : val) :
    rws_OpLib_Op_Coh op v → Serializable (sum_serialization vl_serialization vl_serialization) v.
  Proof. intros Heq. rewrite Heq; destruct op; apply _. Qed.

  Definition rws_OpLib_State_Coh :=
    λ (st : rwsSt vl) v, ∃ (cntsl rmsl : list (vl * vector_clock)) cntsw rmsw,
        v = PairV cntsw rmsw ∧
          (is_list cntsl cntsw ∧ ∀ vtm : vl * Time, vtm ∈ (contents st) ↔ vtm ∈ cntsl) ∧
          (is_list rmsl rmsw ∧ ∀ vtm : vl * Time, vtm ∈ (removes st) ↔ vtm ∈ rmsl).

  Global Instance rws_OpLib_Params : OpLib_Params (rwsOp vl) (rwsSt vl) :=
  {|
    OpLib_Serialization := (sum_serialization vl_serialization vl_serialization);
    OpLib_State_Coh := rws_OpLib_State_Coh;
    OpLib_Op_Coh := rws_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := rws_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := rws_OpLib_Coh_Ser
  |}.

  Lemma rws_init_st_fn_spec : ⊢ init_st_fn_spec init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    iApply "HΦ".
    iPureIntro; eexists [], [], _, _; split_and!; [done|done|set_solver|done|set_solver].
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

  Lemma rws_effect_spec : ⊢ effect_spec effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect.
    destruct log_ev as [log_ev orig vc].
    destruct Hev as (evpl&evvc&evorig& ?&Hopcoh&?&?).
    destruct Hevs as (Hnin & Hmax & Hext).
    destruct Hst as (cntsl&rmsl&cntsw&rmsw&->&[Hcntsl_il Hcntsl]&[Hrmsl_il Hrmsl]).
    simplify_eq/=.
    rewrite Hopcoh /=.
    wp_pures.
    destruct log_ev; wp_pures.
    - rewrite /effect_add_op.
      wp_pures.
      wp_apply (wp_list_fold
                  (A := vl * vector_clock)
                  (λ l w, ⌜w = #(bool_decide (¬ ∃ r, r ∈ l ∧ r.1 = v ∧ ¬ vector_clock_lt r.2 vc))⌝)
                  (λ _, True)
                  (λ _, True)
               )%I; [|iSplit; first done|].
      { iIntros ([w w_tm] acc lacc lrem) "!#".
        iIntros (Ψ) "(->&->&_) HΨ".
        wp_pures.
        destruct (decide (∃ r, (r ∈ lacc ∧ r.1 = v ∧ ¬ vector_clock_lt r.2 vc)))
          as [([u u_tm] & Hu_in & Hu_val & Hutm_lt)|Hnorem]; simpl in *.
        - rewrite !bool_decide_eq_false_2;
            [|intros Hnot; apply Hnot; set_solver|intros Hnot; apply Hnot; set_solver].
          wp_pures.
          iApply "HΨ"; done.
        - rewrite (bool_decide_eq_true_2 (¬ ∃ r, (r ∈ lacc ∧ r.1 = v ∧ ¬ vector_clock_lt r.2 vc)));
            last done.
          wp_pures.
          wp_op; first by rewrite bin_op_eval_eq_val.
          destruct (decide (w = v)) as [->|].
          + rewrite (bool_decide_eq_true_2 (_ = _)); last done.
            wp_pures.
            wp_apply wp_vect_leq;
              first by iPureIntro; split; [apply vector_clock_to_val_is_vc|done].
            iIntros (? ->).
            iApply "HΨ".
            rewrite /time /=.
            destruct (decide (vector_clock_le w_tm vc)) as [Hle|Hnle].
            * rewrite bool_decide_eq_true_2; last done.
              rewrite bool_decide_eq_true_2; first done.
              intros ([z z_tm] & Hz_in & Hz_cal & Hz_lt); simplify_eq/=.
              rewrite elem_of_app elem_of_list_singleton in Hz_in.
              destruct Hz_in as [Hzin|]; simplify_eq /=; [by eauto|].
              apply vector_clock_le_eq_or_lt in Hle as [->|]; last done.
              assert ((v, vc) ∈ lacc ++ (v, vc) :: lrem) as Hv_vc by set_solver.
              apply Hrmsl in Hv_vc.
              apply Hs in Hv_vc as ([z z_orig z_tm] & Hrm_ev_in & Hrm_ev_val & Hrm_ev_vc);
                simplify_eq/=.
              assert ({| EV_Op := Remove v; EV_Orig := z_orig; EV_Time := vc |} =
                      {| EV_Op := remove_wins_set_proof.Add v; EV_Orig := orig; EV_Time := vc |});
                last done.
              apply Hext; [set_solver|set_solver|done].
            * rewrite bool_decide_eq_false_2; last done.
              rewrite bool_decide_eq_false_2; first done.
              intros Hnot; apply Hnot.
              exists (v, w_tm); split_and!; [set_solver|done|].
              intros ?%vector_clock_lt_le; done.
          + rewrite (bool_decide_eq_false_2 (_ = _)); last by apply not_inj.
            wp_pures.
            iApply "HΨ".
            rewrite bool_decide_eq_true_2; first done.
            intros ([z z_tm] & Hz_in & Hz_val & Hz_nlt); simplify_eq/=.
            rewrite elem_of_app elem_of_list_singleton in Hz_in.
            destruct Hz_in as [Hzin|]; [|by simplify_eq /=].
            apply Hnorem; eauto. }
      { rewrite bool_decide_eq_true_2; first done. intros (?&?&?); set_solver. }
      iIntros (?) "[-> _]".
      wp_pures.
      destruct (decide (∃ r, (r ∈ rmsl ∧ r.1 = v ∧ ¬ vector_clock_lt r.2 vc))) as [Hremex|Hremnex].
      + rewrite bool_decide_eq_false_2; last tauto.
        wp_pures.
        iApply "HΦ".
        iExists {| contents := contents log_st; removes := removes log_st|}.
        iPureIntro; split; first by eexists _, _, _, _.
        rewrite /op_rws_effect /update_state /=; f_equal; [].
        rewrite bool_decide_eq_true_2; first done.
        destruct Hremex as (r&?&?&?).
        exists r; split_and!; [|done|done].
        apply elem_of_elements, Hrmsl; done.
      + rewrite bool_decide_eq_true_2; last tauto.
        wp_pures.
        replace ($v, evvc)%V with ($(v, vc) : val)
          by by simpl; f_equal; apply is_vc_vector_clock_to_val.
        wp_apply wp_list_cons; first done.
        iIntros (w Hw).
        wp_pures.
        iApply "HΦ".
        iExists {| contents := {[(v, vc)]} ∪ contents log_st; removes := removes log_st|}.
        iPureIntro; split.
        * eexists _, _, _, _; simpl; split_and!; [done|done| |done|done].
          clear -Hcntsl; set_solver.
        * rewrite /op_rws_effect /update_state /=; f_equal; [].
          rewrite bool_decide_eq_false_2; first done.
          intros (r&Helem&?&?); apply Hremnex.
          exists r; split_and!; [|done|done].
          apply elem_of_elements, Hrmsl in Helem; done.
    - rewrite /effect_remove_op.
      wp_pures.
      replace ($v, evvc)%V with ($(v, vc) : val)
          by by simpl; f_equal; apply is_vc_vector_clock_to_val.
      wp_apply wp_list_cons; first done.
      iIntros (w Hw).
      wp_pures.
      wp_apply (wp_list_filter _ (λ '(z, z_tm), bool_decide (z ≠ v ∨ vector_clock_le vc z_tm))).
      { iSplit; last done.
        iIntros ([z z_tm]) "!#".
        iIntros (Ψ) "_ HΨ".
        wp_pures.
        wp_op; first by rewrite bin_op_eval_eq_val.
        destruct (decide (z = v)) as [->|].
        - rewrite ((bool_decide_eq_true_2 (_ = _))); last done.
          wp_pures.
          wp_apply wp_vect_leq; first by iPureIntro; split; [|apply vector_clock_to_val_is_vc].
          iIntros (? ->).
          iApply "HΨ".
          rewrite /time /=.
          destruct (decide (vector_clock_le vc z_tm)).
          + rewrite !bool_decide_eq_true_2; [done|by right|done].
          + rewrite !bool_decide_eq_false_2; [done|intros [|]; done|done].
        - rewrite ((bool_decide_eq_false_2 (_ = _))); last by apply not_inj.
          wp_pures.
          iApply "HΨ".
          rewrite bool_decide_eq_true_2; [done|by left]. }
      iIntros (rv Hrv).
      wp_pures.
      iApply "HΦ".
      iExists {| contents :=
                  filter (λ '(z, z_tm), z ≠ v ∨ vector_clock_le vc z_tm) (contents log_st);
                removes := {[(v, vc)]} ∪  removes log_st|}.
      iPureIntro; split.
      + eexists _, _, _, _; simpl; split_and!; [done|done| |done|set_solver].
        intros (z, z_tm).
        rewrite elem_of_filter elem_of_list_filter Hcntsl bool_decide_spec; done.
      + rewrite /op_rws_effect /update_state /=; f_equal; [].
        apply set_eq; intros [].
        rewrite !elem_of_filter; clear; firstorder.
  Qed.

  Lemma rws_crdt_fun_spec : ⊢ crdt_fun_spec rws_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /rws_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply rws_init_st_fn_spec; done.
    - iApply rws_effect_spec; done.
  Qed.

  Lemma rws_init_spec :
    init_spec
      (oplib_init
         (s_ser (s_serializer (sum_serialization vl_serialization vl_serialization)))
         (s_deser (s_serializer (sum_serialization vl_serialization vl_serialization)))) -∗
    init_spec_for_specific_crdt 
      (rws_init (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /rws_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply rws_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End rws_proof.

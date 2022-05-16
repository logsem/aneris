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
From aneris.examples.crdt.oplib.examples.prod_comb Require Import prod_comb_code.

Section prodCrdt.
  Context `{!Log_Time}
          `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}
          `(crdt_denotA : !CrdtDenot opA stA)
          `(crdt_denotB : !CrdtDenot opB stB).

  Definition prodOp : Type := opA * opB.
  Definition prodSt : Type := stA * stB.

  Definition prod_denot (s : gset (Event prodOp)) (st : prodSt) : Prop :=
    crdt_denot (gset_map (event_map fst) s) st.1 ∧ crdt_denot (gset_map (event_map snd) s) st.2.

  Global Instance prod_denot_fun : Rel2__Fun prod_denot.
  Proof.
    constructor; intros ? [] [] [] []; simpl in *; f_equal; eapply @rel2_fun; eauto; apply _.
  Qed.

  Global Instance prod_denot_instance : CrdtDenot prodOp prodSt := {
    crdt_denot := prod_denot;
  }.
End prodCrdt.

Global Arguments prodOp _ _ : clear implicits.
Global Arguments prodSt _ _ : clear implicits.


(* TODO: move to the right place. *)
Lemma events_ext_map `{!Log_Time} {Op1 Op2} `{EqDecision Op1} `{Countable Op1}
      `{EqDecision Op2} `{Countable Op2} (f : Op1 → Op2) s :
  events_ext s → events_ext (gset_map (event_map f) s).
Proof.
  intros Hext ? ? [e1 [-> He1]]%gset_map_correct2 [e2 [-> He2]]%gset_map_correct2 Hes.
  f_equal.
  apply Hext; done.
Qed.

Lemma events_total_map `{!Log_Time} {Op1 Op2} `{EqDecision Op1} `{Countable Op1}
      `{EqDecision Op2} `{Countable Op2} (f : Op1 → Op2) s :
  events_total_order s → events_total_order (gset_map (event_map f) s).
Proof.
  intros Htot ? ? [e1 [-> He1]]%gset_map_correct2 [e2 [-> He2]]%gset_map_correct2 Hes Horig.
  simpl in *.
  apply Htot; [done| done | | done].
  intros ->.
  apply Hes; reflexivity.
Qed.

Section OpProd.
  Context `{!Log_Time}
          `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}
          `{crdt_denotA : !CrdtDenot opA stA}
          `{crdt_denotB : !CrdtDenot opB stB}
          `(!OpCrdtModel opA stA)
          `(!OpCrdtModel opB stB).

  Definition op_prod_effect (st : prodSt stA stB) (ev : Event (prodOp opA opB)) st' : Prop :=
    op_crdtM_effect st.1 (event_map fst ev) st'.1 ∧
    op_crdtM_effect st.2 (event_map snd ev) st'.2.

  Lemma op_prod_effect_fun st : Rel2__Fun (op_prod_effect st).
  Proof.
    constructor; intros ? [] [] [] []; simpl in *; f_equal; eapply op_crdtM_effect_fun; eauto.
  Qed.

  Instance op_prod_effect_coh : OpCrdtEffectCoh op_prod_effect.
  Proof.
    intros s e [st1 st2] [st'1 st'2].
    intros [] Hnotin Hmax Hext Htot; split; intros [Hst1 Hst2]; split; simpl in *;
      revert Hst1 Hst2; rewrite ?gset_map_union ?gset_map_singleton; intros Hst1 Hst2.
    - eapply op_crdt_effect_coh; [done| | | | |done].
      + intros [ev [Hev1 Hev2]]%gset_map_correct2.
        assert (e = ev); last set_solver.
        apply Hext; [set_solver|set_solver|].
        pose proof (f_equal time Hev1); destruct e; destruct ev; done.
      + split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hmax; set_solver.
        * by apply irreflexive_eq.
      + apply (events_ext_map fst) in Hext; rewrite gset_map_union gset_map_singleton in Hext; done.
      + apply (events_total_map fst) in Htot; rewrite gset_map_union gset_map_singleton in Htot; done.
    - eapply op_crdt_effect_coh; [done| | | | |done].
      + intros [ev [Hev1 Hev2]]%gset_map_correct2.
        assert (e = ev); last set_solver.
        apply Hext; [set_solver|set_solver|].
        pose proof (f_equal time Hev1); destruct e; destruct ev; done.
      + split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hmax; set_solver.
        * by apply irreflexive_eq.
      + apply (events_ext_map snd) in Hext; rewrite gset_map_union gset_map_singleton in Hext; done.
      + apply (events_total_map snd) in Htot; rewrite gset_map_union gset_map_singleton in Htot; done.
    - eapply op_crdt_effect_coh; [done| | | | |done].
      + intros [ev [Hev1 Hev2]]%gset_map_correct2.
        assert (e = ev); last set_solver.
        apply Hext; [set_solver|set_solver|].
        pose proof (f_equal time Hev1); destruct e; destruct ev; done.
      + split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hmax; set_solver.
        * by apply irreflexive_eq.
      + apply (events_ext_map fst) in Hext; rewrite gset_map_union gset_map_singleton in Hext; done.
      + apply (events_total_map fst) in Htot; rewrite gset_map_union gset_map_singleton in Htot; done.
    - eapply op_crdt_effect_coh; [done| | | | |done].
      + intros [ev [Hev1 Hev2]]%gset_map_correct2.
        assert (e = ev); last set_solver.
        apply Hext; [set_solver|set_solver|].
        pose proof (f_equal time Hev1); destruct e; destruct ev; done.
      + split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hmax; set_solver.
        * by apply irreflexive_eq.
      + apply (events_ext_map snd) in Hext; rewrite gset_map_union gset_map_singleton in Hext; done.
      + apply (events_total_map snd) in Htot; rewrite gset_map_union gset_map_singleton in Htot; done.
  Qed.

  Definition op_prod_init_st : stA * stB := (op_crdtM_init_st, op_crdtM_init_st).

  Lemma op_prod_init_st_coh : ⟦ (∅ : gset (Event (prodOp opA opB))) ⟧ ⇝ op_prod_init_st.
  Proof. split; apply op_crdtM_init_st_coh. Qed.

  Global Instance op_ctr_model_instance : OpCrdtModel (prodOp opA opB) (prodSt stA stB) := {
    op_crdtM_effect := op_prod_effect;
    op_crdtM_effect_fun := op_prod_effect_fun;
    op_crdtM_effect_coh := op_prod_effect_coh;
    op_crdtM_init_st := op_prod_init_st;
    op_crdtM_init_st_coh := op_prod_init_st_coh
  }.

End OpProd.

From aneris.examples.crdt.oplib.proof Require Import time.

Section prod_proof.
  Context `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params, OPPA : !OpLib_Params opA stA, OPPB : !OpLib_Params opB stB}.
  Context `{!OpLib_Res (prodOp opA opB)}.

  Definition prod_OpLib_Op_Coh :=
    λ (op : prodOp opA opB) v,
      ∃ v1 v2, v = PairV v1 v2 ∧ OpLib_Op_Coh op.1 v1 ∧ OpLib_Op_Coh op.2 v2.

  Lemma prod_OpLib_Op_Coh_Inj (o1 o2 : prodOp opA opB) (v : val) :
    prod_OpLib_Op_Coh o1 v → prod_OpLib_Op_Coh o2 v → o1 = o2.
  Proof.
    intros (v11 & v12 & ? & Hv11 & Hv12) (v21 & v22 & ? & Hv21 & Hv22); simplify_eq.
    destruct o1; destruct o2; f_equal; eapply OpLib_Op_Coh_Inj; eauto.
  Qed.

  Lemma prod_OpLib_Coh_Ser (op : prodOp opA opB) (v : val) :
    prod_OpLib_Op_Coh op v →
    Serializable
      (prod_serialization (@OpLib_Serialization _ _ _ _ OPPA) (@OpLib_Serialization _ _ _ _ OPPB)) v.
  Proof.
    intros (v11 & v12 & ? & Hv11 & Hv12); simplify_eq.
    destruct op; simpl in *.
    eexists _, _; split_and!; first done; eapply OpLib_Coh_Ser; eauto.
  Qed.


  Definition prod_OpLib_State_Coh :=
    λ (st : prodSt stA stB) v,
      ∃ v1 v2, v = PairV v1 v2 ∧ OpLib_State_Coh st.1 v1 ∧ OpLib_State_Coh st.2 v2.

  Global Instance prod_OpLib_Params : OpLib_Params (prodOp opA opB) (prodSt stA stB) :=
  {|
    OpLib_Serialization :=
      prod_serialization (@OpLib_Serialization _ _ _ _ OPPA) (@OpLib_Serialization _ _ _ _ OPPB);
    OpLib_State_Coh := prod_OpLib_State_Coh;
    OpLib_Op_Coh := prod_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := prod_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := prod_OpLib_Coh_Ser
  |}.

  Lemma prod_init_st_fn_spec initA initB :
    @init_st_fn_spec _ _ _ _ _ _ _ OPPA initA -∗
    @init_st_fn_spec _ _ _ _ _ _ _ OPPB initB -∗
    @init_st_fn_spec _ _ _ _ _ _ _ prod_OpLib_Params (λ: <>, (initA #(), initB #())).
  Proof.
    iIntros "#HA #HB" (addr).
    iIntros "!#" (Φ) "_ HΦ".
    wp_pures.
    wp_apply "HB"; first done.
    iIntros (vB HvB).
    wp_apply "HA"; first done.
    iIntros (vA HvA).
    wp_pures.
    iApply "HΦ".
    iPureIntro; eexists _, _; eauto.
  Qed.

  (* TODO: move *)
  Canonical Structure vc_time.

  Definition effect_applied (effectA effectB : val) : val :=
    λ: "msg" "state",
        let: "delta1" := Fst (Fst (Fst "msg")) in
        let: "delta2" := Snd (Fst (Fst "msg")) in
        let: "vc" := Snd (Fst "msg") in
        let: "origin" := Snd "msg" in
        let: "st1" := Fst "state" in
        let: "st2" := Snd "state" in
        (effectA ("delta1", "vc", "origin") "st1", effectB ("delta2", "vc", "origin") "st2").

  Lemma prod_effect_spec effectA effectB :
    @effect_spec _ _ _ _ _ _ _ OPPA effectA -∗
    @effect_spec _ _ _ _ _ _ _ OPPB effectB -∗
    @effect_spec _ _ _ _ _ _ _ prod_OpLib_Params (effect_applied effectA effectB).
  Proof.
    iIntros "#HA #HB" (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect_applied.
    destruct log_ev as [[op1 op2] orig vc].
    destruct log_st as [log_st1 log_st2].
    destruct Hst as (st1&st2&?&?&?).
    destruct Hev as (evpl&evvc&evorig&?& (ev1&ev2&?&?&?) &?&?).
    destruct Hs as [Hs1 Hs2].
    simplify_eq/=.
    wp_pures.
    set (es2 := {| EV_Op := op2; EV_Time := vc; EV_Orig := orig|}).
    wp_apply ("HB" $! _ _ _ _ es2).
    { iPureIntro; split_and!; eauto.
      - eexists _, _, _; split_and!; eauto.
      - intros [es [Heseq Hes]]%gset_map_correct2; apply Hevs.
        assert (es = {| EV_Op := (op1, op2); EV_Orig := orig; EV_Time := vc |}).
        { apply Hevs; [set_solver|set_solver|]. pose proof (f_equal time Heseq); done. }
        simplify_eq; done.
      - split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hevs; set_solver.
        * by apply irreflexive_eq.
      - destruct Hevs as (?&?& Hext&?).
        apply (events_ext_map snd) in Hext;
          rewrite gset_map_union gset_map_singleton in Hext; done.
      - destruct Hevs as (?&?&?&Htot).
        apply (events_total_map snd) in Htot;
          rewrite gset_map_union gset_map_singleton in Htot; done. }
    iIntros (vB [st2' [HvB Hst2']]).
    set (es1 := {| EV_Op := op1; EV_Time := vc; EV_Orig := orig|}).
    wp_pures.
    wp_apply ("HA" $! _ _ _ _ es1).
    { iPureIntro; split_and!; eauto.
      - eexists _, _, _; split_and!; eauto.
      - intros [es [Heseq Hes]]%gset_map_correct2; apply Hevs.
        assert (es = {| EV_Op := (op1, op2); EV_Orig := orig; EV_Time := vc |}).
        { apply Hevs; [set_solver|set_solver|]. pose proof (f_equal time Heseq); done. }
        simplify_eq; done.
      - split; first set_solver.
        intros ev; rewrite elem_of_union elem_of_singleton; intros [Hin| ->].
        * apply gset_map_correct2 in Hin as [ev' [-> Hev']].
          apply Hevs; set_solver.
        * by apply irreflexive_eq.
      - destruct Hevs as (?&?& Hext&?).
        apply (events_ext_map fst) in Hext;
          rewrite gset_map_union gset_map_singleton in Hext; done.
      - destruct Hevs as (?&?& ?&Htot).
        apply (events_total_map fst) in Htot;
          rewrite gset_map_union gset_map_singleton in Htot; done. }
    iIntros (vA [st1' [HvA Hst1']]).
    wp_pures.
    iApply "HΦ".
    iExists (_, _).
    iPureIntro.
    split.
    - eexists _, _; split_and!; eauto.
    - split; done.
  Qed.

  Definition prod_comb_crdt_applied (crdtA crdtB : val) : val :=
    λ: <>,
       let: "res1" := crdtA #() in
       let: "res2" := crdtB #() in
       let: "is1" := Fst "res1" in
       let: "eff1" := Snd "res1" in
       let: "is2" := Fst "res2" in
       let: "eff2" := Snd "res2" in
       (init_st "is1" "is2", effect "eff1" "eff2").

  Lemma prod_crdt_fun_spec crdtA crdtB :
    @crdt_fun_spec _ _ _ _ _ _ _ OPPA crdtA -∗
    @crdt_fun_spec _ _ _ _ _ _ _ OPPB crdtB -∗
    @crdt_fun_spec _ _ _ _ _ _ _ prod_OpLib_Params (prod_comb_crdt_applied crdtA crdtB).
  Proof.
    iIntros "#HA #HB" (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /prod_comb_crdt_applied.
    wp_pures.
    wp_apply "HA"; first done.
    iIntros (vA) "HvA".
    wp_pures.
    wp_apply "HB"; first done.
    iIntros (vB) "HvB".
    wp_pures.
    iDestruct "HvA" as (initA effectA ->) "#[HinitA HeffectA]".
    iDestruct "HvB" as (initB effectB ->) "#[HinitB HeffectB]".
    wp_pures.
    rewrite /effect /init_st.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply prod_init_st_fn_spec; done.
    - iApply prod_effect_spec; done.
  Qed.

  Notation prod_comb_init' :=
    (prod_comb_init
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ OPPA)))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ OPPA)))
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ OPPB)))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ OPPB)))).

  Notation oplib_init' :=
    (oplib_init
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ prod_OpLib_Params)))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ prod_OpLib_Params)))).

  Lemma prod_init_spec crdtA crdtB :
    @crdt_fun_spec _ _ _ _ _ _ _ OPPA crdtA -∗
    @crdt_fun_spec _ _ _ _ _ _ _ OPPB crdtB -∗
    @init_spec _ _ _ _ _ _ _ prod_OpLib_Params _ _ oplib_init' -∗
    ∀ (repId : nat) (addr : socket_address) (fixedAddrs : gset socket_address)
      (addrs_val : val),
        {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
            ⌜CRDT_Addresses !! repId = Some addr⌝ ∗
            ⌜addr ∈ fixedAddrs⌝ ∗
            fixed fixedAddrs ∗
            ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ OpLib_SocketProto i) ∗
            addr ⤳ (∅, ∅) ∗
            free_ports (ip_of_address addr) {[port_of_address addr]} ∗
            OpLib_InitToken repId
        }}}
          prod_comb_init' crdtA crdtB addrs_val #repId @[ip_of_address addr]
        {{{ get_state_val update_val, RET (get_state_val, update_val);
            LocState repId ∅ ∅ ∗
            @get_state_spec _ _ _ _ _ _ _ prod_OpLib_Params _ _ get_state_val repId addr ∗
            @update_spec _ _ _ _ _ _ _ prod_OpLib_Params _ _ update_val repId addr
        }}}.
    Proof.
      iIntros "#HA #HB #Hinit" (repId addr fixedAddrs addrs_val).
      iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
      rewrite /prod_comb_init /prod_comb_crdt.
      wp_pures.
      wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
      { do 3 (iSplit; first done). iApply prod_crdt_fun_spec; done. }
      iIntros (get update) "(HLS & #Hget & #Hupdate)".
      wp_pures.
      iApply "HΦ".
      eauto with iFrame.
    Qed.

End prod_proof.

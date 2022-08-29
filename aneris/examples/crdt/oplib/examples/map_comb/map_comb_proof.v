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
From aneris.examples.crdt.oplib.examples.map_comb Require Import map_comb_code.

Section mapCrdt.
  Context `{!Log_Time}
          `{!EqDecision vop} `{!Countable vop}
          `{!CrdtDenot vop vst}.

  Definition mapOp : Type := string * vop.
  Definition mapSt : Type := gmap string vst.

  Definition map_denot (s : gset (Event mapOp)) (state : mapSt) : Prop :=
    dom state = gset_map (λ ev, (EV_Op ev).1) s ∧
    ∀ k vs, state !! k = Some vs →
            crdt_denot (gset_map (event_map snd) (filter (λ ev, (EV_Op ev).1 = k) s)) vs.

  Global Instance map_denot_fun : Rel2__Fun map_denot.
  Proof.
    constructor; intros evs m1 m2 [Hm1dom Hm1] [Hm2dom Hm2].
    apply map_eq; intros k.
    destruct (decide (k ∈ dom m1)) as [Hid|Hnid].
    - pose proof Hid as [vs Hvs]%elem_of_dom.
      rewrite Hm1dom -Hm2dom in Hid.
      pose proof Hid as [vs' Hvs']%elem_of_dom.
      rewrite Hvs Hvs'; f_equal.
      eapply crdt_denot_fun; eauto.
    - pose proof Hnid as ->%not_elem_of_dom.
      rewrite Hm1dom -Hm2dom in Hnid.
      pose proof Hnid as ->%not_elem_of_dom.
      done.
  Qed.

  Global Instance map_denot_instance : CrdtDenot mapOp mapSt := {
    crdt_denot := map_denot;
  }.
End mapCrdt.

Global Arguments mapOp _ : clear implicits.
Global Arguments mapSt _ : clear implicits.

(* TODO: move these lemmas to the right place. *)
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
Lemma events_total_filter `{!Log_Time} {Op} `{!EqDecision Op} `{!Countable Op}
      (P : Event Op → Prop) `{!∀ ev, Decision (P ev)} s :
  events_total_order s → events_total_order (filter P s).
Proof.
  intros Hs ev ev'; rewrite !elem_of_filter; intros [? ?] [? ?] ?; apply Hs; done.
Qed.
Lemma maximal_map `{!Log_Time} {Op1 Op2} `{EqDecision Op1} `{Countable Op1}
      `{EqDecision Op2} `{Countable Op2} (f : Op1 → Op2) ev s :
  maximal ev s → maximal (event_map f ev) (gset_map (event_map f) s).
Proof.
  intros [Hin Hmax]; split.
  - apply gset_map_correct1; done.
  - intros ev' [ev'' [-> Hev'']]%gset_map_correct2.
    apply Hmax; done.
Qed.
Lemma maximal_filter `{!Log_Time} {Op} `{!EqDecision Op} `{!Countable Op}
      (P : Event Op → Prop) `{!∀ ev, Decision (P ev)} ev s :
  P ev → maximal ev s → maximal ev (filter P s).
Proof.
  intros Hev Hs; split.
  - apply elem_of_filter; split; [done|apply Hs].
  - intros ? [? ?]%elem_of_filter; apply Hs; done.
Qed.
Lemma events_total_singleton `{!Log_Time} {Op} `{!EqDecision Op} `{!Countable Op}
      (ev : Event Op) : events_total_order {[ev]}.
Proof.
  intros ?? ?%elem_of_singleton ?%elem_of_singleton; simplify_eq; done.
Qed.

Lemma maximal_singleton `{!Log_Time} {Op} `{!EqDecision Op} `{!Countable Op}
      (ev : Event Op) : maximal ev {[ev]}.
Proof.
  split; first set_solver.
  intros ? ?%elem_of_singleton; subst; apply irreflexivity, _.
Qed.

Section OpMap.
  Context `{!Log_Time}
          `{!EqDecision vop} `{!Countable vop}
          `{!CrdtDenot vop vst}
          `(!OpCrdtModel vop vst).

  Definition op_map_effect (st : mapSt vst) (ev : Event (mapOp vop)) (st' : mapSt vst) : Prop :=
    (∀ k, k ≠ (EV_Op ev).1 → st !! k = st' !! k) ∧
    ∃ vs, st' !! (EV_Op ev).1 = Some vs ∧
    op_crdtM_effect (default op_crdtM_init_st (st !! (EV_Op ev).1)) (event_map snd ev) vs.

  Lemma op_map_effect_fun st : Rel2__Fun (op_map_effect st).
  Proof.
    constructor.
    intros ev m1 m2 (Hm1nev & vs & Hvs1 & Hvs2) (Hm2nev & vs' & Hvs'1 & Hvs'2).
    unfold mapSt in *.
    apply map_eq; intros k.
    destruct (decide (k = (EV_Op ev).1)) as [->|Hneq].
    - rewrite Hvs1 Hvs'1; f_equal. eapply op_crdtM_effect_fun; done.
    - rewrite -Hm1nev // -Hm2nev //.
  Qed.

  Instance op_map_effect_coh : OpCrdtEffectCoh op_map_effect.
  Proof.
    intros s ev m m' [Hsmdom Hsm] Hevs Hmax Hext Htot.
    unfold mapSt in *.
    split.
    - intros (Hmevm'nev & vs & Hvs1 & Hvs2).
      split.
      + rewrite gset_map_union gset_map_singleton /=.
        rewrite -Hsmdom.
        apply set_eq; intros k.
        rewrite elem_of_union elem_of_singleton.
        destruct (decide (k = (EV_Op ev).1)) as [->|].
        * split; first by eauto.
          unfold mapSt in *.
          intros ?; eapply (elem_of_dom_2 (D := gset string)); done.
        * rewrite (elem_of_dom (D := gset string) m' k).
          rewrite (elem_of_dom (D := gset string) m k).
          rewrite Hmevm'nev; last done; tauto.
      + intros k vs' Hvs'.
        destruct (decide ((EV_Op ev).1 = k)) as [<-|]; last first.
        { rewrite filter_union_L gset_map_union filter_singleton_not_L // gset_map_empty right_id_L.
          destruct (m !! k) as [vs''|] eqn:Hvs''.
          - rewrite Hmevm'nev in Hvs''; last done. simplify_eq.
            rewrite -Hmevm'nev in Hvs'; last done.
            apply Hsm; done.
          - rewrite Hmevm'nev in Hvs''; last done. simplify_eq. }
        assert (gset_map
                  (event_map snd)
                  (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) (s ∪ {[ev]})) =
                  gset_map
                    (event_map snd)
                    (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) s) ∪ {[event_map snd ev]})
          as Hmaps_eq.
        { rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton //. }
        simplify_eq.
        destruct (m !! (EV_Op ev).1) as [vs'|] eqn:Hvs'.
        * rewrite Hvs' /= in Hvs2.
          pose proof (Hsm _ _ Hvs').
          rewrite Hmaps_eq.
          eapply op_crdtM_effect_coh; [done| | | | |done].
          -- intros [ev' [? Hev']]%gset_map_correct2.
             apply elem_of_filter in Hev' as [Hev't Hev'].
             assert (ev = ev'); last by subst; set_solver.
             apply Hext; [set_solver|set_solver|].
             destruct ev; destruct ev'; simplify_eq/=; done.
          -- rewrite -Hmaps_eq.
             apply maximal_map.
             apply maximal_filter; done.
          -- rewrite -Hmaps_eq.
             apply events_ext_map.
             apply events_ext_filter; done.
          -- rewrite -Hmaps_eq.
             apply events_total_map.
             apply events_total_filter; done.
        * rewrite Hmaps_eq.
          pose proof Hvs' as Hnid%not_elem_of_dom.
          rewrite Hsmdom in Hnid.
          assert (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) s = ∅) as ->.
          { apply set_eq; intros ev'; split; last set_solver.
            intros [Hvaleq ?]%elem_of_filter.
            exfalso; apply Hnid.
            rewrite -Hvaleq.
            apply (gset_map_correct1 (λ ev, (EV_Op ev).1)); done. }
          rewrite gset_map_empty.
          rewrite Hvs' /= in Hvs2.
          eapply op_crdtM_effect_coh; [apply op_crdtM_init_st_coh|set_solver| | | |done].
          -- rewrite left_id_L; apply maximal_singleton.
          -- rewrite left_id_L; apply events_ext_singleton.
          -- rewrite left_id_L; apply events_total_singleton.
    - intros [Hdom Hvals]; split.
      + intros k Hk.
        destruct (m !! k) as [vs|] eqn:Hvs.
        * pose proof Hvs as Hkm%elem_of_dom_2.
          rewrite Hsmdom in Hkm.
          assert (k ∈ dom m') as Hkm'
              by by rewrite gset_map_union in Hdom; set_solver.
          apply elem_of_dom in Hkm' as [vs' Hvs'].
          rewrite Hvs Hvs'; f_equal.
          eapply crdt_denot_fun; [|by apply Hvals].
          rewrite filter_union_L gset_map_union filter_singleton_not_L // gset_map_empty right_id_L.
          apply Hsm; done.
        * pose proof Hvs as Hkm%not_elem_of_dom.
          rewrite Hsmdom in Hkm.
          assert (k ∉ dom m') as Hkm'.
          { rewrite gset_map_union gset_map_singleton in Hdom. set_solver. }
          apply not_elem_of_dom in Hkm'.
          rewrite Hvs Hkm'; done.
      + assert ((EV_Op ev).1 ∈ dom m') as Hvs.
        { rewrite Hdom gset_map_union gset_map_singleton; set_solver. }
        apply elem_of_dom in Hvs as [vs Hvs].
        eexists; split; first done.
        destruct (m !! (EV_Op ev).1) as [vs'|] eqn:Hvs'.
        * rewrite Hvs' /=.
          assert (gset_map
                    (event_map snd) (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) (s ∪ {[ev]})) =
                    gset_map
                      (event_map snd)
                      (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) s) ∪ {[event_map snd ev]})
            as Hmaps_eq.
          { rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton //. }
          eapply op_crdtM_effect_coh; [by apply Hsm| | | | |by rewrite -Hmaps_eq; auto].
          -- intros (ev' & ? & [? Hev']%elem_of_filter)%gset_map_correct2.
             destruct ev as [[] ]; destruct ev' as [[] ]; simplify_eq/=; done.
          -- rewrite -Hmaps_eq.
             apply maximal_map.
             apply maximal_filter; done.
          -- rewrite -Hmaps_eq.
             apply events_ext_map.
             apply events_ext_filter; done.
          -- rewrite -Hmaps_eq.
             apply events_total_map.
             apply events_total_filter; done.
        * rewrite Hvs' /=.
          assert (filter (λ ev', (EV_Op ev').1 = (EV_Op ev).1) s = ∅) as Hfilterempty.
          { apply set_eq; intros ev'; split; last set_solver.
            intros [Hvaleq ?]%elem_of_filter.
            apply not_elem_of_dom in Hvs'.
            rewrite Hsmdom in Hvs'.
            exfalso; apply Hvs'.
            rewrite -Hvaleq.
            apply (gset_map_correct1 (λ ev, (EV_Op ev).1)); done. }
          specialize (Hvals _ _ Hvs).
          rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton in Hvals.
          rewrite Hfilterempty in Hvals.
          rewrite gset_map_empty in Hvals.
          eapply op_crdtM_effect_coh; [apply op_crdtM_init_st_coh|set_solver| | | |done].
          -- rewrite left_id_L; apply maximal_singleton.
          -- rewrite left_id_L; apply events_ext_singleton.
          -- rewrite left_id_L; apply events_total_singleton.
  Qed.

  Definition op_map_init_st : mapSt vst := ∅.

  Lemma op_map_init_st_coh : ⟦ (∅ : gset (Event (mapOp vop))) ⟧ ⇝ op_map_init_st.
  Proof.
    split.
    - unfold mapSt.
      rewrite /op_map_init_st dom_empty_L gset_map_empty; done.
    - set_solver.
  Qed.

  Global Instance op_map_model_instance : OpCrdtModel (mapOp vop) (mapSt vst) := {
    op_crdtM_effect := op_map_effect;
    op_crdtM_effect_fun := op_map_effect_fun;
    op_crdtM_effect_coh := op_map_effect_coh;
    op_crdtM_init_st := op_map_init_st;
    op_crdtM_init_st_coh := op_map_init_st_coh
  }.

End OpMap.

From aneris.aneris_lang.lib Require Import map_code map_proof.
From aneris.examples.crdt.oplib.proof Require Import time.

Section map_proof.
  Context `{!EqDecision vop} `{!Countable vop}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params, OPP : !OpLib_Params vop vst}.
  Context `{!OpLib_Res (mapOp vop)}.

  Definition map_OpLib_Op_Coh :=
    λ (op : mapOp vop) v, ∃ v1 v2, v = PairV v1 v2 ∧ v1 = #op.1 ∧ OpLib_Op_Coh op.2 v2.

  Lemma map_OpLib_Op_Coh_Inj (o1 o2 : mapOp vop) (v : val) :
    map_OpLib_Op_Coh o1 v → map_OpLib_Op_Coh o2 v → o1 = o2.
  Proof.
    intros (v11 & v12 & ? & Hv11 & Hv12) (v21 & v22 & ? & Hv21 & Hv22); simplify_eq.
    destruct o1; destruct o2; f_equal; last eapply OpLib_Op_Coh_Inj; eauto.
  Qed.

  Lemma map_OpLib_Coh_Ser (op : mapOp vop) (v : val) :
    map_OpLib_Op_Coh op v →
    Serializable
      (prod_serialization string_serialization (@OpLib_Serialization _ _ _ _ OPP)) v.
  Proof.
    intros (v11 & v12 & ? & Hv11 & Hv12); simplify_eq.
    destruct op; simpl in *.
    eexists _, _; split_and!; [done|apply serializable|eapply OpLib_Coh_Ser; eauto].
  Qed.


  Definition map_OpLib_State_Coh :=
    λ (st : mapSt vst) v,
      ∃ (m : gmap string val), is_map v m ∧
      dom m = dom st ∧
      ∀ k vs w, m !! k = Some w → st !! k = Some vs → OpLib_State_Coh vs w.

  Global Instance map_OpLib_Params : OpLib_Params (mapOp vop) (mapSt vst) :=
  {|
    OpLib_Serialization :=
      prod_serialization string_serialization (@OpLib_Serialization _ _ _ _ OPP);
    OpLib_State_Coh := map_OpLib_State_Coh;
    OpLib_Op_Coh := map_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := map_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := map_OpLib_Coh_Ser
  |}.

  Lemma map_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _ _ map_OpLib_Params map_comb_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /map_comb_init_st.
    wp_pures.
    wp_apply wp_map_empty; first done.
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro.
    exists ∅; split_and!;
           [done|rewrite /op_crdtM_init_st /= /op_map_init_st /mapSt; set_solver| set_solver].
  Qed.

  (* TODO: move *)
  Canonical Structure vc_time.

  Definition effect_applied (init eff : val) : val :=
    λ: "msg" "state",
      let: "key" := Fst (Fst (Fst "msg")) in
      let: "delta" := Snd (Fst (Fst "msg")) in
      let: "vc" := Snd (Fst "msg") in
      let: "origin" := Snd "msg" in
      let: "cur_st_wo" := match: map_lookup "key" "state" with
                            NONE => (init #(), "state")
                          | SOME "cur" => ("cur", map_remove "key" "state")
                          end in
      let: "current" := Fst "cur_st_wo" in
      let: "state_without" := Snd "cur_st_wo" in
      let: "newval" := eff ("delta", "vc", "origin") "current" in
      map_insert "key" "newval" "state_without".

  Lemma map_effect_spec init effect :
    @init_st_fn_spec _ _ _ _ _ _ _ OPP init -∗
    @effect_spec _ _ _ _ _ _ _ OPP effect -∗
    @effect_spec _ _ _ _ _ _ _ map_OpLib_Params (effect_applied init effect).
  Proof.
    iIntros "#Hinit #Heff" (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect_applied.
    destruct log_ev as [[key vl] orig vc].
    destruct Hst as (mp & Hmp & Hdom & Hvls).
    destruct Hev as (evpl&evvc&evorig&?& (ev1&ev2&?&?&?) &?&?).
    destruct Hevs as (Hnin & Hmax & Hext & Htot).
    destruct Hs as [Hdom' Hvls'].
    subst.
    wp_pures.
    wp_apply (wp_map_lookup (K := string) (V := val)); first done.
    iIntros (w Hw).
    destruct (mp !! key) as [cur|] eqn:Hcureq; subst.
    - wp_pures.
      wp_apply (wp_map_remove (K := string) (V := val)); first done.
      iIntros (st' Hst').
      wp_pures.
      assert (key ∈ dom log_st) as Hkeyst by by rewrite -Hdom; apply elem_of_dom.
      unfold mapSt in *.
      apply elem_of_dom in Hkeyst as [curst Hcurst].
      wp_apply ("Heff" $! _ _ _ _ {|EV_Op := vl; EV_Orig := orig; EV_Time := vc|} curst).
      { iPureIntro; split_and!; eauto.
        - eexists _, _, _; split_and!; eauto.
        - intros [ev [Heveq [? Hev]%elem_of_filter]]%gset_map_correct2.
          rewrite /event_map in Heveq.
          destruct ev as [[? vl'] ]; simplify_eq/=; done.
        - apply (maximal_filter (λ ev, (EV_Op ev).1 = key)) in Hmax; last done.
          apply (maximal_map snd) in Hmax.
          rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton in Hmax;
            done.
        - apply (events_ext_filter _ (λ ev, (EV_Op ev).1 = key)) in Hext.
          apply (events_ext_map _ snd) in Hext.
          rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton in Hext;
            done.
        - apply (events_total_filter (λ ev, (EV_Op ev).1 = key)) in Htot.
          apply (events_total_map snd) in Htot.
          rewrite filter_union_L gset_map_union filter_singleton_L // gset_map_singleton in Htot;
            done.
      }
      iIntros (st'' (newst & Hnewstcoh & Hnewst_effct)).
      wp_pures.
      wp_apply (wp_map_insert (K := string) (V := val) _ key st'' st'); first done.
      iIntros (mp' Hmp').
      iApply "HΦ".
      iExists (<[key := newst]> log_st).
      iPureIntro; split.
      + eexists _; split_and!; first done.
        * unfold mapSt.
          rewrite !dom_insert_L dom_delete_L.
          rewrite Hdom.
          rewrite [{[_]} ∪ _]comm_L.
          rewrite difference_union_L; clear; set_solver.
        * unfold mapSt.
          intros k vs w.
          destruct (decide (k = key)) as [->|].
          -- rewrite !lookup_insert; intros ? ?; simplify_eq; done.
          -- rewrite !lookup_insert_ne // lookup_delete_ne //.
             apply Hvls.
      + split; simpl.
        * unfold mapSt.
          intros ? ?; rewrite lookup_insert_ne; done.
        * unfold mapSt.
          eexists; split; first by rewrite lookup_insert.
          rewrite Hcurst /=; done.
    - wp_pures.
      wp_apply "Hinit"; first done.
      iIntros (ist Hist).
      wp_pures.
      wp_apply ("Heff" $! _ _ _ _ {|EV_Op := vl; EV_Orig := orig; EV_Time := vc|} op_crdtM_init_st).
      { iPureIntro; split_and!; eauto.
        - eexists _, _, _; split_and!; eauto.
        - apply op_crdtM_init_st_coh.
        - set_solver.
        - rewrite left_id_L. apply maximal_singleton.
        - rewrite left_id_L. apply events_ext_singleton.
        - rewrite left_id_L. apply events_total_singleton. }
      iIntros (st' (newst & Hnewstcoh & Hnewst_effct)).
      wp_pures.
      wp_apply (wp_map_insert (K := string) (V := val) _ key st' st); first done.
      iIntros (mp' Hmp').
      iApply "HΦ".
      iExists (<[key := newst]> log_st).
      iPureIntro; split.
      + eexists _; split_and!; first done.
        * unfold mapSt.
          rewrite !dom_insert_L Hdom //.
        * unfold mapSt.
          intros k vs w.
          destruct (decide (k = key)) as [->|].
          -- rewrite !lookup_insert; intros ? ?; simplify_eq; done.
          -- rewrite !lookup_insert_ne //.
             apply Hvls.
      + split; simpl.
        * unfold mapSt.
          intros ? ?; rewrite lookup_insert_ne; done.
        * unfold mapSt.
          eexists; split; first by rewrite lookup_insert.
          apply not_elem_of_dom in Hcureq.
          rewrite Hdom in Hcureq.
          unfold mapSt in Hcureq.
          apply not_elem_of_dom in Hcureq.
          rewrite Hcureq /=; done.
  Qed.

  Definition map_comb_crdt_applied (crdt : val) : val :=
    λ: <>,
       let: "res" := crdt #() in
       let: "is" := Fst "res" in
       let: "eff" := Snd "res" in
       (map_comb_init_st, map_comb_effect "is" "eff").

  Lemma map_crdt_fun_spec crdt :
    @crdt_fun_spec _ _ _ _ _ _ _ OPP crdt -∗
    @crdt_fun_spec _ _ _ _ _ _ _ map_OpLib_Params (map_comb_crdt_applied crdt).
  Proof.
    iIntros "#Hcrdt" (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /map_comb_crdt_applied.
    wp_pures.
    wp_apply "Hcrdt"; first done.
    iIntros (w) "Hw".
    wp_pures.
    iDestruct "Hw" as (init effect ->) "#[Hinit Heffect]".
    wp_pures.
    rewrite /map_comb_effect /map_comb_init_st.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply map_init_st_fn_spec; done.
    - iApply map_effect_spec; done.
  Qed.

  Notation map_comb_init' :=
    (map_comb_init
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ OPP)))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ OPP)))).

  Notation oplib_init' :=
    (oplib_init
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ map_OpLib_Params)))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ map_OpLib_Params)))).

  Lemma map_init_spec crdt :
    @crdt_fun_spec _ _ _ _ _ _ _ OPP crdt -∗
    @init_spec _ _ _ _ _ _ _ map_OpLib_Params _ _ oplib_init' -∗
    ∀ (repId : nat) (addr : socket_address)
      (addrs_val : val),
        {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
            ⌜CRDT_Addresses !! repId = Some addr⌝ ∗
            ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ OpLib_SocketProto i) ∗
            addr ⤳ (∅, ∅) ∗
            free_ports (ip_of_address addr) {[port_of_address addr]} ∗
            OpLib_InitToken repId
        }}}
          map_comb_init' crdt addrs_val #repId @[ip_of_address addr]
        {{{ get_state_val update_val, RET (get_state_val, update_val);
            LocState repId ∅ ∅ ∗
            @get_state_spec _ _ _ _ _ _ _ map_OpLib_Params _ _ get_state_val repId addr ∗
            @update_spec _ _ _ _ _ _ _ map_OpLib_Params _ _ update_val repId addr
        }}}.
    Proof.
      iIntros "#Hcrdt #Hinit" (repId addr addrs_val).
      iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
      rewrite /map_comb_init /map_comb_crdt.
      wp_pures.
      wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
      { do 2 (iSplit; first done). iApply map_crdt_fun_spec; done. }
      iIntros (get update) "(HLS & #Hget & #Hupdate)".
      wp_pures.
      iApply "HΦ"; eauto.
    Qed.

End map_proof.

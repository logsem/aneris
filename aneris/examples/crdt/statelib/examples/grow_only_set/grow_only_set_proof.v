From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.prelude Require Import misc strings.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import list_proof set_proof inject.
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
From aneris.examples.crdt.statelib.examples.grow_only_set Require Import grow_only_set_code.


Section gos_denot.
  Context `{!CRDT_Params} `{!Log_Time}.
  Context `{!EqDecision vl, !Countable vl}.

  (** Definition of operations and states. *)
  Definition gos_op : Type := vl.
  Definition gos_st : Type := gset vl.

  (** Definition of the denotation. *)
  Definition gos_denot_prop (s: event_set gos_op) (st: gos_st) :=
    gset_map (fun (ev: Event gos_op) => ev.(EV_Op)) s = st.

  Global Instance gos_denot_fun : Rel2__Fun gos_denot_prop.
  Proof.
    constructor; unfold gos_denot_prop; intros s st st' Hst Hst'.
    by rewrite -Hst -Hst'.
  Qed.

  Global Instance gos_denot : CrdtDenot gos_op gos_st :=
    { crdt_denot     := gos_denot_prop;
      crdt_denot_fun := gos_denot_fun; }.

End gos_denot.

Section gos_model.
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl, !Countable vl}.

  Definition gos_mut (st: @gos_st gos_op _ _) (ev: Event gos_op) (st': gos_st) : Prop :=
    st' = st ∪ {[ev.(EV_Op)]}.

  Lemma gos_mut_mon (st : gos_st) (e: Event gos_op) (st': gos_st) :
    gos_mut st e st' → st ≤_l st'.
  Proof. set_solver. Qed.

  Lemma gos_mut_coh (s : event_set gos_op) (st st' : gos_st) (ev: Event gos_op) :
    ⟦ s ⟧ ⇝ st ->
    Lst_Validity' s ->
    Lst_Validity' (s∪{[ev]}) ->
    ev ∉ s ->
    is_maximum ev (s ∪ {[ ev ]}) ->
    gos_mut st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st'.
  Proof.
    rewrite /=/gos_denot_prop /gos_mutator.
    intros ???? _ ->. by set_solver.
  Qed.

  Lemma gos_lub_coh
        (s1 s2 : event_set gos_op) (st1 st2 st3 : (@gos_st gos_op _ _)):
    ⟦ s1 ⟧ ⇝ st1 → ⟦ s2 ⟧ ⇝ st2
    → Lst_Validity' s1 → Lst_Validity' s2 → Lst_Validity' (s1 ∪ s2)
    → (∀ (i: nat), fil s1 i ⊆ fil s2 i ∨ fil s2 i ⊆  fil s1 i)
    → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    rewrite /=/gos_denot_prop.
    intros <- <- Hval1 Hval2 Hval _ <-.
    by rewrite gset_map_union.
  Qed.

  Definition gos_st_init : (@gos_st gos_op _ _) := ∅.

  Lemma gos_init_coh : ⟦ ∅ ⟧ ⇝ gos_st_init.
  Proof. by set_solver. Qed.

  Global Instance gos_model : (StateCrdtModel gos_op gos_st) :=
    { st_crdtM_lub_coh     := gos_lub_coh;
      st_crdtM_mut         := gos_mut;
      st_crdtM_mut_mon     := gos_mut_mon;
      st_crdtM_mut_coh     := gos_mut_coh;
      st_crdtM_init_st     := gos_st_init;
      st_crdtM_init_st_coh := gos_init_coh; }.

End gos_model.

Section gos_proof.
  Context (E : serialization).
  Context `{!Inject vl val}.
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl, !Countable vl}.
  Context `{anerisG Mdl Σ}.

  Definition gos_op_coh (op: gos_op) (v: val) : Prop := v = $op ∧ s_valid_val E $ v.

  Lemma gos_op_coh_inj (o o': gos_op) (v: val) :
    gos_op_coh o v -> gos_op_coh o' v -> o = o'.
  Proof.
    intros (Hv & _) (Hv' & _).
    rewrite/gos_op_coh in Hv. rewrite/gos_op_coh in Hv'.
    by simplify_eq/=.
  Qed.

  Definition gos_st_coh (st: (@gos_st vl _ _)) (v: val) : Prop :=
    is_set st v ∧ (∀ elt, elt ∈ st → s_valid_val E $ elt).

  Lemma gos_st_coh_inj (st st': gos_st) (v: val) :
    gos_st_coh st v -> gos_st_coh st' v -> st = st'.
  Proof.
    intros ((l & Hv & Hst & Hd) & _) ((l' & Hv' & Hst' & Hd') & _).
    apply is_list_inject in Hv, Hv'.
    subst.
    f_equal.
    by apply Inject_list.(inject_inj) in Hv'.
  Qed.

  Lemma gos_st_coh_serializable :
    ∀ (st : gos_st) (v : val),
    gos_st_coh st v → Serializable (list_serialization E) v.
  Proof.
    rewrite /gos_st_coh.
    intros st v ((l & Hl & Hl2) & Hs).
    exists l. split; first done.
    intros x Hx. set_solver.
  Qed.

  Global Instance gos_coh_params : (@StLib_Coh_Params gos_op (@gos_st vl _ _) ) :=
    {
      StLib_StSerialization := list_serialization E;
      StLib_Op_Coh          := gos_op_coh;
      StLib_Op_Coh_Inj      := gos_op_coh_inj;
      StLib_St_Coh          := gos_st_coh;
      StLib_St_Coh_Inj      := gos_st_coh_inj;
      StLib_StCoh_Ser       := gos_st_coh_serializable
 }.

  Global Instance gos_params : (StLib_Params gos_op (@gos_st vl _ _) ) :=
    {
      StLib_Denot           := gos_denot;
      StLib_Model           := gos_model;
      StLib_CohParams       := gos_coh_params;
    }.


  Lemma gos_init_st_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _ _ _ _ gos_params gos_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /gos_init_st.
    wp_pures.
    wp_apply (wp_set_empty vl); first done.
    iIntros (v Hv).
    iApply "HΦ".
    destruct Hv as (l & Hl & Heq & Hn).
    rewrite -list_to_set_nil in Heq.
    simpl; rewrite /gos_st_coh /gos_st_init.
    destruct l as [|x l]; last first.
    { simpl in Heq. assert (x ∉ (∅ : gset vl)) as Habs.
      set_solver. rewrite Heq in Habs. set_solver. }
    iPureIntro.
    rewrite Hl.
    simpl in *.
    split_and!; [by exists [] | set_solver].
  Qed.

  Lemma gos_mutator_st_spec :
    ⊢ @mutator_spec _ _ _ _ _ _ _ _ _ gos_params gos_mutator.
  Proof.
    iIntros (sa f st_v op_v s ev op_log st_log)
            "!> %φ ((-> & %Hvv) & (%Hst_coh & %Hst_coh') & %Hden &
                    %Hnin & <- & <- & %Hmax & %Hext & %Hsoc) Hφ".
    wp_lam. wp_pures.
    wp_apply (wp_set_add $! Hst_coh).
    iIntros (v Hv).
    iApply "Hφ". simplify_eq /=.
    iExists ({[EV_Op ev]} ∪ st_log).
    iPureIntro.
    split; last by set_solver.
    split; set_solver.
  Qed.

  Lemma gos_merge_spec : ⊢ @merge_spec _ _ _ _ _ _ _ _ _ gos_params gos_merge.
  Proof.
    iIntros (sa v v' s s' st st')
            "!> %φ (%Hcoh_st & %Hcoh_st' & %Hden & %Hden' &
                    %Hext & %Hsoc & %Hext' & %Hsoc') Hφ".
    destruct Hcoh_st as (Hst & Hvv).
    destruct Hcoh_st' as (Hst' & Hvv').
    wp_lam.
    wp_let.
    wp_apply (wp_set_union _ st st' v v'); first by eauto.
    iIntros (u Hu).
    iApply "Hφ".
    iExists (st ∪ st').
    iSplit; last done.
    iPureIntro.
    split; first done.
    destruct Hu as (lu & Hlu & HluX & Hndup).
    by set_solver.
    Qed.

  Lemma gos_crdt_fun_spec : ⊢ @crdt_fun_spec _ _ _ _ _ _ _ _ _ gos_params gos_crdt.
  Proof.
    iIntros (sa φ) "!> _ Hφ".
    wp_lam; wp_pures. iApply "Hφ".
    iExists gos_init_st, gos_mutator, gos_merge.
    iSplit; first trivial.
    iDestruct gos_init_st_spec as "Hinit".
    iDestruct gos_merge_spec as "Hmerge".
    iDestruct gos_mutator_st_spec as "Hmutator".
    iFrame "Hinit Hmerge Hmutator".
  Qed.

  Lemma gos_init_spec `{!StLib_Res (@gos_op vl)}:
    @init_spec
      _ _ _ _ _ _ _ _ _  gos_params _
      (statelib_init (list_ser (s_serializer E).(s_ser)) (list_deser (s_serializer E).(s_deser))) -∗
    init_spec_for_specific_crdt (gos_init (s_serializer E).(s_ser) (s_serializer E).(s_deser)).
  Proof.
    iIntros "#Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /gos_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply gos_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & Hget & Hupdate)".
    wp_pures.
    iApply "HΦ"; iFrame.
  Qed.

End gos_proof.


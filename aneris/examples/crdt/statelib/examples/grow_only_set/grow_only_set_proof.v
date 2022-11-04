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
  Context `{!vl : Type}.
  Context `{!CRDT_Params} `{!Log_Time}.
  Context `{!EqDecision vl} `{!Countable vl}.

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

  Global Instance gset_subset_po : PartialOrder  (⊆@{gset vl}).
  Proof. repeat split; repeat intro; multiset_solver. Qed.

  Lemma gset_union_lub_spec :
    ∀ e1 e2 : gos_st, e1 ⊆ e1 ∪ e2 ∧
                        e2 ⊆ e1 ∪ e2 ∧
                        (∀ e : gos_st, e1 ⊆ e → e2 ⊆ e → e1 ∪ e2 ⊆ e).
  Proof. repeat split; repeat intro; multiset_solver. Qed.


  (** Instantiation of the Join-Semi-Lattice. *)
  Global Instance gos_st_le_lat : Lattice gos_st :=
    { lat_le := (⊆);
      lat_po := gset_subset_po;
      lat_lub := (∪);
      lat_lub_spec := gset_union_lub_spec }.

End gos_denot.

Section gos_model.
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl} `{!Countable vl}.
  Context `{!EventSetValidity vl}.


  Definition gos_mutator
             (st: @gos_st gos_op _ _) (ev: Event gos_op) (st': gos_st) : Prop :=
    st' = st ∪ {[ev.(EV_Op)]}.

  Lemma gos_mut_mon (st : gos_st) (e: Event gos_op) (st': gos_st) :
    gos_mutator st e st' → st ≤_l st'.
  Proof. set_solver. Qed.

  Lemma gos_mut_coh
        (s : event_set gos_op) (st st' : gos_st) (ev: Event gos_op) :
    ⟦ s ⟧ ⇝ st ->
    event_set_valid s ->
    ev ∉ s ->
    is_maximum ev (s ∪ {[ ev ]}) ->
    gos_mutator st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st'.
  Proof.
    rewrite /=/gos_denot_prop /gos_mutator.
    intros ???? ->. by set_solver.
  Qed.

  Lemma gos_lub_coh
        (s1 s2 : event_set gos_op) (st1 st2 st3 : (@gos_st gos_op _ _)):
    ⟦ s1 ⟧ ⇝ st1 → ⟦ s2 ⟧ ⇝ st2
    → event_set_valid s1 → event_set_valid s2 → event_set_valid (s1 ∪ s2)
    → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    rewrite /=/gos_denot_prop.
    intros <- <- Hval1 Hval2 Hval <-.
    by rewrite gset_map_union.
  Qed.

  Definition gos_st_init : (@gos_st gos_op _ _) := ∅.

  Lemma gos_init_coh : ⟦ ∅ ⟧ ⇝ gos_st_init.
  Proof. by set_solver. Qed.

  Global Instance gos_model : (StateCrdtModel gos_op gos_st) :=
    { st_crdtM_lub_coh     := gos_lub_coh;
      st_crdtM_mut         := gos_mutator;
      st_crdtM_mut_mon     := gos_mut_mon;
      st_crdtM_mut_coh     := gos_mut_coh;
      st_crdtM_init_st     := gos_st_init;
      st_crdtM_init_st_coh := gos_init_coh; }.

End gos_model.

(* TODO : move to the lib. *)
Section list_serialization.

  Context (E : serialization).
  Context `{!Inject A val}.

  Fixpoint list_valid_val_aux (la : list A) :=
    match la with
    | hd :: tl => s_valid_val E $ hd ∧ list_valid_val_aux tl
    | [] => True
    end.

  Definition list_valid_val (v : val) :=
    ∃ (la: list A), is_list la v ∧ list_valid_val_aux la.

  Fixpoint list_is_ser_aux (la : list A) (s : string) :=
    match la with
      | hd :: tl =>
          ∃ s1 s2 : string,
            E.(s_is_ser) $hd s1 ∧
            s = prod_ser_str s1 s2 ∧
            list_is_ser_aux tl s2
      | [] => s = ""
  end.

  Definition list_is_ser (v : val) (s : string) :=
    ∃ (la : list A),
      is_list la v ∧ list_valid_val_aux la ∧ list_is_ser_aux la s.

  Lemma list_is_ser_valid (v : val) (s : string) :
    list_is_ser v s -> list_valid_val v.
  Proof. destruct 1 as (?&?&?&?). by eexists. Qed.


  Lemma list_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜list_valid_val v⌝ }}}
      (list_serializer (s_serializer E)).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜list_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    iLöb as "IH" forall (Φ v).
    wp_rec.
    iDestruct "Hv" as %(l&Hvl&Hvv).
    destruct l as [|a l].
    - rewrite Hvl.
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      rewrite /list_is_ser; eexists []; done.
    - simpl in Hvl, Hvv.
      destruct Hvl as [lv [-> Hvl]].
      destruct Hvv as [Hva Hvv].
      wp_pures.
      wp_apply (s_ser_spec E); first done.
      iIntros (s1) "%Hs1".
      wp_pures.
      wp_bind (list_ser (s_ser (s_serializer E)) _).
      iApply "IH"; [iPureIntro; eexists; done |].
      iIntros "!>" (s2) "%Hs2".
      wp_pures.
      destruct Hs2 as (l'&Hs2x&Hs2y&Hs2z).
      iApply "HΦ".
      iPureIntro.
      exists (a :: l').
      split; first by eexists.
      split; first by eexists.
      by exists s1, s2.
  Qed.

  Lemma list_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜list_is_ser v s⌝ }}}
      (list_serializer (s_serializer E)).(s_deser) #s @[ip]
      {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "Hs HΦ".
    iLöb as "IH" forall (Φ v s).
    wp_rec.
    iDestruct "Hs" as %(l&Hl1&Hl2&Hl3).
    destruct l as [|a l]; simpl.
    - rewrite Hl1 Hl3.
      wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
      wp_pures.
      by iApply "HΦ".
    - destruct Hl1 as [lv [-> Hl1]].
      destruct Hl2 as (Hvv2 & Hl2).
      destruct Hl3 as (s1&s2&Hs1&->&Hl3).
      rewrite! /prod_ser_str.
      wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
      erewrite (index_0_append_char ); auto; last first.
      { apply valid_tag_stringOfZ. }
      wp_pures.
      wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
      rewrite substring_0_length_append.
      wp_pure _.
      { simpl. rewrite ZOfString_inv //. }
      wp_apply wp_unSOME; [done|].
      iIntros "_ /=". wp_pures.
      wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      replace (Z.to_nat (Z.add (Z.of_nat
                                  (String.length
                                     (StringOfZ (Z.of_nat (String.length s1)))))
                               1%Z)) with
        (String.length (StringOfZ (Z.of_nat (String.length s1))) + 1)%nat by lia.
      replace (Z.to_nat (String.length s1)) with (String.length s1)%nat by lia.
      rewrite substring_add_length_app /= substring_0_length_append.
      wp_pures.
      rewrite !length_app /=.
      match goal with
      | |- context [Substring _ _ ?X] =>
          replace X with (Val #(String.length s2)); last first
      end.
    { repeat f_equal; lia. }
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    match goal with
    | |- context [substring ?X _ _] =>
      replace X with (String.length
                        (StringOfZ (Z.of_nat (String.length s1))) + 1 +
                        String.length s1)%nat by lia
    end.
    rewrite -plus_assoc substring_add_length_app /= substring_length_append.
    wp_pures.
    wp_apply (s_deser_spec E); first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_bind (list_deser _ _).
    iApply ("IH" $! _ lv); first by iPureIntro; eexists.
    iIntros "!> _".
    wp_pures.
    wp_apply (wp_list_cons _ l); first done.
    iIntros (v Hl).
    assert ((InjRV ($ a, lv) = v)) as ->.
    { destruct Hl as [lv' [-> Hl1']].
      by rewrite (is_list_eq _ _ _ Hl1 Hl1'). }
    by iApply "HΦ".
  Qed.

Definition list_serialization : serialization :=
  {| s_valid_val := list_valid_val;
     s_serializer := list_serializer E.(s_serializer);
     s_is_ser := list_is_ser;
     s_is_ser_valid := list_is_ser_valid;
     s_ser_spec := @list_ser_spec;
     s_deser_spec := @list_deser_spec; |}.

End list_serialization.

Section gos_params.
  Context (E : serialization).
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl} `{!Countable vl}.
  Context `{!EventSetValidity vl}.
  Context `{!Inject vl val}.

  Definition gos_op_coh (op: gos_op) (v: val) : Prop := v = $op.

  Lemma gos_op_coh_inj (o o': gos_op) (v: val) :
    gos_op_coh o v -> gos_op_coh o' v -> o = o'.
  Proof.
    intros Hv Hv'.
    rewrite/gos_op_coh in Hv. rewrite/gos_op_coh in Hv'.
    by simplify_eq/=.
  Qed.

  Definition gos_st_coh (st: (@gos_st vl _ _)) (v: val) : Prop :=
    v = inject_list (elements st) ∧ list_valid_val E v.

  Lemma gos_st_coh_inj (st st': gos_st) (v: val) :
    gos_st_coh st v -> gos_st_coh st' v -> st = st'.
  Proof.
    intros (Hv & _) (Hv' & _).
    rewrite/gos_st_coh in Hv Hv'.
    simplify_eq.
    apply Inject_list.(inject_inj) in Hv'.
    apply set_eq.
    intros x. by rewrite - !elem_of_elements Hv'.
  Qed.

  Lemma gos_st_coh_serializable :
    ∀ (st : gos_st) (v : val),
    gos_st_coh st v → Serializable (list_serialization E) v.
  Proof.
    rewrite /gos_st_coh.
    intros st v (-> & (l & Hl & Hv)).
    exists (elements st).
    apply is_list_inject, Inject_list.(inject_inj) in Hl as ->.
    by split; first by apply is_list_inject.
  Qed.

  Global Instance gos_params : (StLib_Params gos_op (@gos_st vl _ _) ) :=
    {
      StLib_StSerialization := list_serialization E;
      StLib_Denot           := gos_denot;
      StLib_Model           := gos_model;
      StLib_Op_Coh          := gos_op_coh;
      StLib_Op_Coh_Inj      := gos_op_coh_inj;
      StLib_St_Coh          := gos_st_coh;
      StLib_St_Coh_Inj      := gos_st_coh_inj;
      StLib_StCoh_Ser       := gos_st_coh_serializable
 }.

End gos_params.

(* TODO: fix typeclasses instantiation. *)
Section Gos_specs.
  Context (E : serialization).
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl} `{!Countable vl}.
  Context `{!EventSetValidity vl}.
  Context `{!Inject vl val}.

  Lemma gos_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _  _ _ _ _ (gos_params E) init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    wp_apply wp_set_empty; first done.
    iIntros (v Hv).
    iApply "HΦ".
    destruct Hv as (l & Hl & Heq & Hn).
    rewrite -list_to_set_nil in Heq.
    simpl; rewrite /gos_st_coh /gos_st_init elements_empty.
    destruct l as [|x l]; last first.
    { simpl in Heq. assert (x ∉ (∅ : gset vl)) as Habs.
      set_solver. rewrite Heq in Habs. set_solver. }
    iPureIntro.
    rewrite Hl.
    simpl in *.
    split; first done.
    by exists [].
    Unshelve. eauto.
    Unshelve. eauto.
    Unshelve. eauto.
  Qed.

End Gos_specs.

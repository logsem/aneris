From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang.lib Require Import list_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import
     crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
     Require Import semi_join_lattices model params.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.proof
     Require Import events spec.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.aneris_lang.lib.vector_clock
     Require Import vector_clock_code vector_clock_proof.
From aneris.examples.crdt.statelib.examples.gcounter
     Require Import gcounter_code.

Section GCtr_defs.

  Context `{!CRDT_Params}.

  (** Definition of operations and states *)

  Definition gctr_op : Type := nat.
  Definition gctr_st : Type := vec nat (length CRDT_Addresses).

End GCtr_defs.

Section Utils.

  Context `{!CRDT_Params}.

  Definition fold_sum (s: event_set gctr_op) :=
    set_fold (fun (ev: Event gctr_op) v => v + ev.(EV_Op))%nat O s.

  Lemma fold_sum_pos (s: event_set gctr_op) :
    (O ≤ (fold_sum s))%nat.
  Proof. exact (Nat.le_0_l _). Qed.

  Lemma fold_sum_union_le (s s': event_set gctr_op):
    (fold_sum s ≤ fold_sum (s ∪ s'))%nat.
  Proof.
    generalize dependent s'.
    apply set_ind.
    - intros???. split; set_solver.
    - by replace (s ∪ ∅) with s; last set_solver.
    - intros x X Hnin HX.
      destruct (decide (x ∈ s));
        first (replace (s ∪ ({[x]} ∪ X))with(s ∪ X); [assumption | set_solver]).
      replace (s ∪ ({[x]} ∪ X)) with ((s ∪ X) ∪ {[x]}); last set_solver.
      rewrite/fold_sum set_fold_disj_union_strong;
        [ | lia | set_solver].
      rewrite set_fold_singleton.
      pose proof (Nat.le_add_r
                    (set_fold (λ (ev : Event gctr_op) (v : nat), (v + EV_Op ev)%nat) O (s ∪ X))
                    (EV_Op x)).
      by apply Nat.le_trans
        with
        (set_fold (λ (ev : Event gctr_op) (v : nat), (v + EV_Op ev)%nat) O (s ∪ X)).
  Qed.

  Lemma fold_sum_mon (s s': event_set gctr_op):
    s ⊆ s' → (fold_sum s ≤ fold_sum s')%nat.
  Proof.
    intros Hsub.
    rewrite (union_difference_L s s' Hsub).
    rewrite/fold_sum.
    apply fold_sum_union_le.
  Qed.

  Lemma fold_sum_disj_union i s (ev: Event gctr_op):
    ev ∉ s
    → fold_sum (fil s i ∪ {[ev]}) = ((fold_sum (fil s i)) + ev.(EV_Op))%nat.
  Proof.
    intros Hnin.
    rewrite/fold_sum.
    rewrite set_fold_disj_union_strong; [ | lia | set_solver ].
    rewrite set_fold_singleton.
    reflexivity.
  Qed.

  Fixpoint lmap2 {A B C: Type} (f: A -> B -> C) (l: list A) (l': list B): list C :=
    match l, l' with
    | [], _ => []
    | _, [] => []
    | h :: t, h' :: t' => f h h' :: lmap2 f t t'
    end.

  Lemma list_length_Sn {A} (l: list A) (n: nat):
    length l = S n → ∃ (h: A) (t: list A), l = h :: t.
  Proof.
    intros Hlen.
    destruct l as [| h t]; first inversion Hlen.
    by exists h, t.
  Qed.

  Lemma lmap2_length l l' n:
    length l = n →
    length l' = n →
    length (lmap2 Init.Nat.max l l') = length l.
  Proof.
    generalize l l'; clear l l'.
    induction n as [|n'].
    { intros l l' Hlen Hlen'.
      apply nil_length_inv in Hlen as ->.
      by apply nil_length_inv in Hlen' as ->. }
    intros l l' Hlen Hlen'.
    destruct (list_length_Sn l n' Hlen) as (h & t & ->).
    destruct (list_length_Sn l' n' Hlen') as (h' & t' & ->).
    simpl.
    f_equal.
    apply IHn';
      [ by inversion Hlen | by inversion Hlen' ].
  Qed.

  Lemma lmap_lookup (l l': list nat) (n i x y: nat):
    length l = n →
    length l' = n →
    l !! i = Some x →
    l' !! i = Some y →
    lmap2 Init.Nat.max l l' !! i = Some (max x y).
  Proof.
    generalize l l' i; clear l l' i.
    induction n as [ | n' ].
    { intros l l' i Hl Hl' Himp _.
      apply nil_length_inv in Hl as ->. inversion Himp. }
    intros l l' i Hlen Hlen' Hl Hl'.
    destruct (list_length_Sn l n' Hlen) as (h & t & ->).
    destruct (list_length_Sn l' n' Hlen') as (h' & t' & ->).
    destruct i as [ | i' ]; first (inversion Hl; inversion Hl'; reflexivity).
    inversion Hlen as [H1]. inversion Hlen' as [H2].
    simpl.
    rewrite list_lookup_succ in Hl. rewrite list_lookup_succ in Hl'.
    exact (IHn' t t' i' H1 H2 Hl Hl').
  Qed.

  Lemma my_list_lookup (l: list nat) (i: nat):
    i < length l → ∃ x, l !! i = Some x.
  Proof.
    generalize l i; clear l i.
    induction l as [ | h t IH ];
      first ( intros i Hi; inversion Hi ).
    intros [ | i' ] Hi; first by exists h.
    simpl; simpl in Hi; apply Nat.succ_lt_mono in Hi.
    by apply IH.
  Qed.

  Lemma gctr_st_lub_lmap2 (st st': gctr_st):
    lmap2 max st st' = vectn_lub (length CRDT_Addresses) st st'.
  Proof.
    apply list_eq. intros i.
    rewrite/vectn_lub.
    destruct (decide (i < length CRDT_Addresses)).
    - set f := nat_to_fin l.
      pose proof l as l_st; pose proof l as l_st'; pose proof l as l'.
      rewrite -(vec_to_list_length st) in l_st.
      rewrite -(vec_to_list_length st') in l_st'.
      rewrite -(vec_to_list_length (vzip_with Nat.max st st')) in l'.
      destruct (my_list_lookup st i l_st) as [x Hx].
      destruct (my_list_lookup st' i l_st') as [y Hy].
      destruct (my_list_lookup (vec_to_list (vzip_with Nat.max st st')) i l') as [z Hz].
      rewrite (lmap_lookup st st' (length CRDT_Addresses) i x y);
        try assumption; try by apply vec_to_list_length.
      assert(Hv: vzip_with Nat.max st st' !!! f = max (st !!! f) (st' !!! f));
        first by rewrite vlookup_zip_with.
      pose proof Hz as Hz'.
      rewrite -vlookup_lookup' in Hz'.
      destruct Hz' as (Hlt & Hz').
      assert (nat_to_fin Hlt = f) as <-.
      { rewrite/f. apply Fin.of_nat_ext. }
      rewrite Hv in Hz'. rewrite -Hz' in Hz. rewrite Hz.
      assert (st !!! nat_to_fin Hlt = x) as ->;
        first by rewrite vlookup_lookup fin_to_nat_to_fin.
      assert (st' !!! nat_to_fin Hlt = y) as ->;
        [ by rewrite vlookup_lookup fin_to_nat_to_fin | reflexivity ].
    - rewrite lookup_ge_None_2;
      first rewrite lookup_ge_None_2;
        [ reflexivity
        | rewrite vec_to_list_length; lia
        | ].
      rewrite (lmap2_length st st' (length CRDT_Addresses));
        [
        | by rewrite vec_to_list_length
        | by rewrite vec_to_list_length ].
      rewrite vec_to_list_length. lia.
  Qed.

End Utils.

Section GCtr_Denot.

  Context `{!CRDT_Params}.

  (** Definition of the Denotation *)

  Definition gctr_denot_prop (s: event_set gctr_op) (st: gctr_st) :=
    ∀ (i: fin (length CRDT_Addresses)),
      st !!! i = fold_sum (fil s i).

  Global Instance gctr_denot_fun : Rel2__Fun gctr_denot_prop.
  Proof.
    constructor; unfold gctr_denot_prop; intros s st st' Hst Hst'.
    apply vec_eq. intros i. rewrite (Hst i)(Hst' i). reflexivity.
  Qed.

  Global Instance gctr_denot : CrdtDenot gctr_op gctr_st :=
    { crdt_denot     := gctr_denot_prop;
      crdt_denot_fun := gctr_denot_fun; }.

End GCtr_Denot.

(** Definition of the mutator *)
Section GCtr_Model.

  Context `{!CRDT_Params}.

  Lemma gctr_lub_coh
    (s1 s2 : event_set gctr_op) (st1 st2 st3 : gctr_st):
    ⟦ s1 ⟧ ⇝ st1 → ⟦ s2 ⟧ ⇝ st2
    → Lst_Validity s1 → Lst_Validity s2 → Lst_Validity (s1 ∪ s2)
    → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    intros Hden1 Hden2 Hval1 Hval2 Hval <-.
    rewrite/=/gctr_denot_prop/vectn_lub.
    intros i.
    destruct (lst_validity_filtered s1 s2 Hval1 Hval2 Hval i) as [Hincl' | Hincl'].
    - assert (Hincl: fil s2 i = fil (s1 ∪ s2) i); first set_solver.
      rewrite -Hincl vlookup_zip_with.
      assert (Hmax: (st1 !!! i `max` st2 !!! i = st2 !!! i)%nat);
        last by rewrite Hmax (Hden2 i).
      rewrite (Hden1 i) (Hden2 i).
      assert (fil s1 i ⊆ fil s2 i).
      { intros e [He_filter He_in]%elem_of_filter. set_solver. }
      assert (fold_sum (fil s1 i) ≤ fold_sum (fil s2 i))%nat;
        [ by apply fold_sum_mon | lia ].
    - assert (Hincl: fil s1 i = fil (s1 ∪ s2) i); first set_solver.
      rewrite -Hincl vlookup_zip_with.
      assert (Hmax: (st1 !!! i `max` st2 !!! i = st1 !!! i)%nat);
        last by rewrite Hmax (Hden1 i).
      rewrite (Hden1 i) (Hden2 i).
      assert (fil s2 i ⊆ fil s1 i).
      { intros e [He_filter He_in]%elem_of_filter. set_solver. }
      assert (fold_sum (fil s2 i) ≤ fold_sum (fil s1 i))%nat;
        [ by apply fold_sum_mon | lia ].
  Qed.

  Definition gctr_mut
    (st: gctr_st) (ev: Event gctr_op) (st': gctr_st) : Prop :=
    st' =
      match decide (ev.(EV_Orig) < length CRDT_Addresses)%nat with
      | left H  =>
        let f := nat_to_fin H in
        vinsert f (st !!! f + ev.(EV_Op))%nat st
      | right _ => st
      end.

  Lemma gctr_mut_mon
    (st : gctr_st) (e: Event gctr_op) (st': gctr_st) :
    gctr_mut st e st' → st ≤_l st'.
  Proof.
    intros ->.
    destruct (decide (EV_Orig e < length CRDT_Addresses)%nat); last reflexivity.
    apply Forall2_vlookup. intros i.
    simpl.
    destruct (decide (i = nat_to_fin l)) as [-> | Hneq];
      last by rewrite vlookup_insert_ne.
    rewrite vlookup_insert.
    apply Nat.le_add_r.
  Qed.

  Lemma gctr_mut_coh
    (s : event_set gctr_op) (st st' : gctr_st) (ev: Event gctr_op) :
    ⟦ s ⟧ ⇝ st ->
    Lst_Validity s ->
    ev ∉ s ->
    is_maximum ev (s ∪ {[ ev ]}) ->
    gctr_mut st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st'.
  Proof.
    intros Hden Hval Hnin Hmax Hmut.
    intros i.
    destruct (decide (ev.(EV_Orig) = i)).
    - assert (Hfil: fil (s ∪ {[ev]}) i = (fil s i) ∪ {[ev]}); first set_solver.
      rewrite Hmut Hfil.
      destruct (decide (EV_Orig ev < length CRDT_Addresses)%nat);
        last (pose proof (fin_to_nat_lt i); lia).
        assert (i = nat_to_fin l) as <-.
        { apply fin_to_nat_inj. by rewrite -e fin_to_nat_to_fin. }
      simplify_eq/=.
      by rewrite (fold_sum_disj_union _ _ _ Hnin) (Hden i) vlookup_insert.
    - assert (Hfil: fil (s ∪ {[ev]}) i = fil s i); first set_solver.
      rewrite Hmut Hfil.
      destruct (decide (EV_Orig ev < length CRDT_Addresses)%nat);
        last exact (Hden i).
      assert (nat_to_fin l ≠ i)%nat as Hneq.
      { intros Himp. apply n.
        by rewrite -Himp fin_to_nat_to_fin. }
      rewrite /=(Hden (nat_to_fin l)) vlookup_insert_ne;
        [ by rewrite (Hden i) | assumption ].
  Qed.

  Definition gctr_st_init : gctr_st := vreplicate (length CRDT_Addresses) O.

  Lemma gctr_init_coh : ⟦ ∅ ⟧ ⇝ gctr_st_init.
  Proof.
    rewrite/=/gctr_denot_prop/gctr_st_init.
    intros i.
    assert (fil (∅: event_set gctr_op) i = ∅) as Heq;
      first by rewrite/fil filter_empty_L.
    by rewrite Heq vlookup_replicate /fold_sum set_fold_empty.
  Qed.

  Instance gctr_model : (StateCrdtModel gctr_op gctr_st) :=
    { st_crdtM_lub_coh     := gctr_lub_coh;
      st_crdtM_mut         := gctr_mut;
      st_crdtM_mut_mon     := gctr_mut_mon;
      st_crdtM_mut_coh     := gctr_mut_coh;
      st_crdtM_init_st     := gctr_st_init;
      st_crdtM_init_st_coh := gctr_init_coh; }.

End GCtr_Model.

Section GCounter_params.

  Context `{!CRDT_Params}.

  Definition gctr_op_coh (op: gctr_op) (v: val) : Prop := v = #op.

  Lemma gctr_op_coh_inj (o o': gctr_op) (v: val) :
    gctr_op_coh o v -> gctr_op_coh o' v -> o = o'.
  Proof.
    intros Hv Hv'.
    rewrite/gctr_op_coh in Hv. rewrite/gctr_op_coh in Hv'.
    by simplify_eq/=.
  Qed.

  (** Injection *)
  Definition gctr_st_inject {A : Type} {Inject0 : Inject A val}
    (xs : gctr_st) : val :=
    inject_list (vec_to_list xs).

  Global Instance gctr_st_inject_inj {A: Type} : Inj eq eq gctr_st_inject.
  Proof.
    intros x y Heq.
    by apply vec_to_list_inj2, Inject_list.(inject_inj).
  Qed.

  Global Instance Inject_Vec : Inject gctr_st val :=
    { inject     := gctr_st_inject;
      inject_inj := @gctr_st_inject_inj nat }.


  Definition gctr_st_coh (st: gctr_st) (v: val) : Prop :=
    v = gctr_st_inject st.

  Lemma gctr_st_coh_inj (st st': gctr_st) (v: val) :
    gctr_st_coh st v -> gctr_st_coh st' v -> st = st'.
  Proof.
    intros Hv Hv'.
    rewrite/gctr_st_coh in Hv. rewrite/gctr_st_coh in Hv'.
    simplify_eq.
    exact (@gctr_st_inject_inj val st st' Hv').
  Qed.

  (** serialization *)

  Definition gctr_ser : serialization := vc_serialization.

  Lemma gctr_st_coh_is_vc (st: gctr_st):
    is_vc (gctr_st_inject st) st.
  Proof.
    rewrite/gctr_st_inject/is_vc.
    apply is_list_inject. reflexivity.
  Qed.

  Lemma gctr_st_coh_serializable
    (st : gctr_st) (v : val):
    gctr_st_coh st v → Serializable gctr_ser v.
  Proof.
    intros->.
    exists st. exact (gctr_st_coh_is_vc st).
  Qed.

  Global Instance gctr_params : (StLib_Params gctr_op gctr_st) :=
    {
      StLib_StSerialization := gctr_ser;
      StLib_Denot           := gctr_denot;
      StLib_Model           := gctr_model;
      StLib_Op_Coh          := gctr_op_coh;
      StLib_Op_Coh_Inj      := gctr_op_coh_inj;
      StLib_St_Coh          := gctr_st_coh;
      StLib_St_Coh_Inj      := gctr_st_coh_inj;
      StLib_StCoh_Ser       := gctr_st_coh_serializable }.

End GCounter_params.


Section GCounter_Specs.
  Context `{!anerisG M Σ, !CRDT_Params}.

  Lemma gctr_st_coh_is_list log_st v_st:
    gctr_st_coh log_st v_st → is_list log_st v_st.
  Proof. intros->. by apply is_list_inject. Qed.

  Lemma gctr_st_coh_length log_st v_st:
    gctr_st_coh log_st v_st → (length log_st = length CRDT_Addresses)%nat.
  Proof. intros->. by rewrite vec_to_list_length. Qed.

  Lemma max_fn_spec (n n': nat) ip:
    {{{ True }}}
      max_fn #n #n' @[ip]
    {{{ (x: nat), RET #x; ⌜ x = max n n' ⌝ }}}.
  Proof.
    iIntros (φ) "_ Hφ".
    wp_lam. wp_pures.
    destruct (decide (n < n'));
      [ rewrite bool_decide_eq_true_2 | rewrite bool_decide_eq_false_2 ].
    2, 4: lia.
    all: wp_if; iApply "Hφ"; iPureIntro; lia.
  Qed.

  (* TODO: move to the list proof *)
  Lemma wp_list_map2 (l: list nat) (l': list nat) (lv l'v: val) ip:
    {{{ ⌜length l = length l'⌝ ∗
        ⌜is_list l lv⌝ ∗
        ⌜is_list l' l'v⌝
      }}}
      list_map2 max_fn lv l'v @[ip]
    {{{ rv, RET rv;
        let r := lmap2 max l l' in
        ⌜is_list r rv⌝ }}}.
  Proof.
    iLöb as "IH" forall (l l' lv l'v).
    iIntros (φ) "(%Hlen & %Hl & %Hl') Hφ".
    pose proof Hlen as Hlen'.
    wp_lam. wp_pures.
    destruct l as [| h t].
    - rewrite nil_length in Hlen. symmetry in Hlen.
      apply nil_length_inv in Hlen as ->.
      inversion Hl. inversion Hl'.
      wp_match. wp_inj. iApply "Hφ". iPureIntro. reflexivity.
    - simpl in Hlen. symmetry in Hlen.
      apply list_length_Sn in Hlen as (h' & t' & ->).
      inversion Hl as (tv & -> & Htv). inversion Hl' as (t'v & -> & Ht'v).
      do 2 wp_match.
      wp_bind (list_map2 _ _ _).
      wp_pures.
      iApply ("IH" $! t t').
      { iPureIntro. repeat split.
        simpl in Hlen'. apply eq_add_S in Hlen'.
        all: assumption. }
      iNext. iIntros (rv Htail). wp_pures.
      wp_apply max_fn_spec; first trivial.
      iIntros (? ->).
      replace (#(h `max` h')%nat) with ($ (h `max` h')%nat); last done.
      wp_apply wp_list_cons; first (iPureIntro; exact Htail).
      iIntros (v (rv' & -> & Hv)). iApply "Hφ".
      iPureIntro. by exists rv'.
  Qed.

  Lemma Ctr_merge_spec : ⊢ merge_spec gcpt_merge.
  Proof.
    iIntros (sa v v' s s' st st')
            "!> %φ (%Hcoh_st & %Hcoh_st' & %Hden & %Hden' & %Hext & %Hsoc & %Hext' & %Hsoc') Hφ".
    wp_lam. wp_let.
    wp_apply (wp_list_map2 st st' v v').
    - iPureIntro. repeat split;
        [ by do 2 rewrite vec_to_list_length | |];
        by apply gctr_st_coh_is_list.
    - iIntros (rv) "%Hrv".
      iApply "Hφ". iPureIntro.
      exists (st ⊔_l st'). split; last reflexivity.
      simpl. rewrite/gctr_st_coh/gctr_st_inject.
      replace (vec_to_list (vectn_lub (length CRDT_Addresses) st st'))
        with (lmap2 Init.Nat.max st st');
        first by apply is_list_inject in Hrv as ->.
      apply gctr_st_lub_lmap2.
  Qed.


  Lemma Ctr_mutator_spec : ⊢ mutator_spec gcpt_mutator.
  Proof.
    iIntros (sa f st_v op_v s ev op_log st_log)
      "!> %φ (%Hop_coh & %Hst_coh & %Hden & %Hnin & <- & <- & %Hmax & %Hext & %Hsoc) Hφ".
    wp_lam. do 4 wp_pure _.
    wp_bind (list_nth _ _)%E.
    wp_apply (wp_list_nth _ (EV_Orig ev) st_log st_v).
    { iPureIntro. by apply gctr_st_coh_is_list. }
    iIntros (v [[-> Hlen]| (r & -> & Herr)]).
    - wp_match. iApply "Hφ". iPureIntro. exists st_log. split; first assumption.
      rewrite/st_crdtM_mut/StLib_Model/StLib_Params/gctr_params/gctr_model/gctr_mut.
      rewrite (gctr_st_coh_length st_log st_v Hst_coh) in Hlen.
      destruct(decide (EV_Orig ev < length CRDT_Addresses))%nat;
        [ lia | reflexivity ].
    - assert (EV_Orig ev < length st_log)%nat as Hlen_lt;
        first (apply nth_error_Some; by rewrite Herr).
      wp_match.
      rewrite Hop_coh; wp_op.
      assert(#(EV_Op ev + r) = #(EV_Op ev + r)%nat) as ->;
        first by rewrite Nat2Z.inj_add.
      iApply (wp_vect_update _ st_v st_log (EV_Orig ev) (EV_Op ev +r));
        [ lia | iPureIntro; rewrite Hst_coh; by apply gctr_st_coh_is_vc | ].
      iNext.
      iIntros (v Hres).
      iApply "Hφ".
      iPureIntro.
      rewrite (vec_to_list_length st_log) in Hlen_lt.
      exists (vinsert (nat_to_fin Hlen_lt) (EV_Op ev + r) st_log).
      split.
      + rewrite/StLib_St_Coh/gctr_params/gctr_st_coh/gctr_st_inject
          vec_to_list_insert fin_to_nat_to_fin.
        by apply is_list_inject.
      + rewrite/st_crdtM_mut/StLib_Model/gctr_params/gctr_model/gctr_mut
          decide_True_pi Nat.add_comm.
        do 2 f_equal. symmetry.
        apply vlookup_lookup.
        apply misc.nth_error_lookup in Herr. rewrite -Herr.
        f_equal. apply fin_to_nat_to_fin.
  Qed.

   Lemma init_st_coh:
  StLib_St_Coh st_crdtM_init_st
    (inject_list (vreplicate (length CRDT_Addresses) O)).
  Proof. reflexivity. Qed.

  Lemma Ctr_init_st_fn_spec :
    ⊢ init_st_fn_spec (λ: <>, gcpt_init_st #(length CRDT_Addresses) #()).
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /gcpt_init_st.
    wp_pures.
    wp_apply (wp_vect_make _ (length CRDT_Addresses) 0 Φ $! I ).
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro.
    assert (v = (inject_list (vreplicate (length CRDT_Addresses) O))) as ->.
    { rewrite /is_vc in Hv. rewrite -vec_to_list_replicate in Hv.
      by apply is_list_inject. }
    exact init_st_coh.
  Qed.

  Lemma Ctr_crdt_fun_spec :
    ⊢ crdt_fun_spec (λ: <>, gcpt_crdt #(length CRDT_Addresses) #()).
  Proof.
    iIntros (sa φ) "!> _ Hφ".
    wp_lam; wp_pures. wp_lam. wp_pures.
    iApply "Hφ".
    iExists _, gcpt_mutator, gcpt_merge.
    iSplit; first trivial.
    iDestruct Ctr_init_st_fn_spec as "Hinit"; first eauto.
    iDestruct Ctr_merge_spec as "Hmerge".
    iDestruct Ctr_mutator_spec as "Hmutator".
    iFrame "Hinit Hmerge Hmutator".
  Qed.

End GCounter_Specs.

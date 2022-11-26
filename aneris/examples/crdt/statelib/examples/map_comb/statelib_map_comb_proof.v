From aneris.aneris_lang.lib Require Import inject.
From aneris.prelude Require Import gset_map.
From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib Require Import map_code map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec
  Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import spec.
From aneris.examples.crdt.statelib.examples.map_comb
  Require Import statelib_map_comb_code.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.aneris_lang.lib Require Import set_proof.
From aneris.examples.crdt.statelib.proof Require Import events.
From aneris.examples.crdt.statelib.time Require Import maximality.

Lemma map_dom_None {E E'} `{!EqDecision E, !Countable E} (m: gmap E E') u:
  m !! u = None → u ∉ gset_dom m.
Proof. by intros?%not_elem_of_dom. Qed.
Lemma map_dom_Some {E E'} `{!EqDecision E, !Countable E} (m: gmap E E') u v:
  m !! u = Some v → u ∈ gset_dom m.
Proof. by intros?%elem_of_dom_2. Qed.
Lemma map_dom_Some_2 {E E'} `{!EqDecision E, !Countable E} (m: gmap E E') u:
  u ∈ gset_dom m → ∃ v, m !! u = Some v.
Proof. by intros[]%elem_of_dom; exists x. Qed.

Section Bloup.
  Context `{!CRDT_Params}.

  Context (LogOp: Type)
          (eqdec_logop: EqDecision LogOp) (countable_logop: Countable LogOp).
  Context (LogSt: Type) (latA: Lattice LogSt).
  Context (Hcd: @CrdtDenot LogOp LogSt timestamp_time eqdec_logop countable_logop).
  Context (inj_st: Inject LogSt val).

  Context (p: @StLib_Params LogOp LogSt eqdec_logop countable_logop latA _).

  Definition mapSt: Type := gmap string LogSt.
  Definition mapOp: Type := string * LogOp.

  Definition map_lat_le (st1 st2: mapSt) : Prop :=
    ∀ (s: string) (v: LogSt),
      st1 !! s = Some v
      → ∃ (v': LogSt), st2 !! s = Some v' ∧ (latA.(lat_le)) v v'.

  Definition map_lat_le_po: PartialOrder map_lat_le.
  Proof.
    repeat split.
    + intros m s v. by exists v.
    + intros m m' m'' Hle Hle' s v Hms.
      destruct (Hle s v Hms) as (v' & Hm's & Hlev).
      destruct (Hle' s v' Hm's) as (v'' & Hm''s & Hlev').
      exists v''. split; first done.
      destruct latA as [leA [[reflA trA] AntiSymA] lubA lub_propA].
      by apply (trA v v' v'').
    + intros m m' Hle Hle'.
      apply map_eq. intros s.
      destruct (m !! s) as [v|] eqn:E.
      - destruct (Hle s v E) as (v' & Heq & Hle_vv'); rewrite Heq.
        destruct (Hle' s v' Heq) as (v'' & Heq' & Hle_v'v). f_equal.
        destruct latA as [leA [[reflA trA] AntiSymA] lubA lub_propA].
        assert (v'' = v) as ->; first by simplify_eq.
        rewrite Heq'; f_equal.
        by apply (AntiSymA v v').
      - destruct (m' !! s) as [v|] eqn:E'; last by rewrite E E'.
        destruct (Hle' s v E') as (v'' & Ebis & HleA).
        by rewrite Ebis in E.
  Qed.

  (*Definition map_lat_lub (m m': mapSt) : mapSt :=
    let dom0 := gset_dom m in let dom1 := gset_dom m' in let dom := dom0 ∪ dom1 in
    (set_fold
      (λ s acc,
        match gmap_lookup s m with
        | None =>
          match gmap_lookup s m' with
          | None => acc
          | Some v' => map_insert s v' acc
          end
        | Some v =>
          match gmap_lookup s m' with
          | None => map_insert s v acc
          | Some v' => map_insert s (latA.(lat_lub) v v') acc
          end
        end) (gmap_empty: gmap string LogSt) dom).*)

  Definition map_lat_lub (m m': mapSt): mapSt :=
    map_fold (λ s v' acc,
      match acc !! s with
      | None => map_insert s v' acc
      | Some v => map_insert s (latA.(lat_lub)v v') acc
      end) m m'.

  Lemma TODO1 (m: mapSt):
    dom m = (gset_dom m).
  Proof. reflexivity. Qed.
  Lemma TODO0 i v (m: mapSt):
    gset_dom (map_insert i v m) = (gset_dom m) ∪ ({[i]}).
  Proof. do 2rewrite -TODO1.
    apply set_eq. split; rewrite dom_insert; set_solver. Qed.

  Lemma lat_lub_fold_aux i x (m0: mapSt):
    ∀ (j1 j2 : string) (z1 z2 : LogSt) (y : mapSt),
      j1 ≠ j2 → <[i:=x]> m0 !! j1 = Some z1 → <[i:=x]> m0 !! j2 = Some z2 →
      match match y !! j2 with
        | Some v0 => map_insert j2 (v0 ⊔_l z2) y
        | None => map_insert j2 z2 y end !! j1
      with
      | Some v0 => map_insert j1 (v0 ⊔_l z1) match y !! j2 with
        | Some v1 => map_insert j2 (v1 ⊔_l z2) y
        | None => map_insert j2 z2 y end
      | None => map_insert j1 z1 match y !! j2 with
        | Some v0 => map_insert j2 (v0 ⊔_l z2) y
        | None => map_insert j2 z2 y end end =
      match match y !! j1 with
        | Some v0 => map_insert j1 (v0 ⊔_l z1) y
        | None => map_insert j1 z1 y end !! j2
      with
      | Some v0 => map_insert j2 (v0 ⊔_l z2) match y !! j1 with
        | Some v1 => map_insert j1 (v1 ⊔_l z1) y
        | None => map_insert j1 z1 y end
      | None => map_insert j2 z2 match y !! j1 with
        | Some v0 => map_insert j1 (v0 ⊔_l z1) y
        | None => map_insert j1 z1 y end end.
  Proof.
    intros s1 s2 st1 st2 st Hneq Hs1 Hs2.
    destruct(st !! s1)as[e1|]eqn:E1; destruct(st !! s2)as[e2|]eqn:E2;
    destruct(map_insert s2 st2 st !! s1)as[e3|]eqn:E3;
    try (destruct(map_insert s1 (e1 ⊔_l st1) st !! s2)as[e4|]eqn:E4);
    try (destruct(map_insert s2 (e2 ⊔_l st2) st !! s1)as[e5|]eqn:E5);
    try (destruct(map_insert s1 st1 st !! s2)as[e|]eqn:E);
    apply map_eq; intros s; (destruct (decide (s = s1)); [|destruct(decide(s=s2))]);
    simplify_eq/=.
    all: try (rewrite lookup_insert_ne in E3; last done).
    all: try (rewrite lookup_insert_ne in E4; last done).
    all: try (rewrite lookup_insert_ne in E5; last done).
    all: try (rewrite lookup_insert in E3).
    all: try (rewrite lookup_insert in E4).
    all: try (rewrite lookup_insert in E5).
    all: try(rewrite lookup_insert_ne in E; last done).
    all: try rewrite E5 in E1.
    all: try rewrite E2 in E4.
    all: try rewrite E1 in E3.
    all: try rewrite E in E2.
    all: simplify_eq/=.
    all: try ((rewrite lookup_insert lookup_insert_ne; last done);
      by rewrite lookup_insert).
    all: by do 4 (rewrite lookup_insert_ne; last done).
  Qed.


  Lemma map_lat_lub_dom (m m': mapSt):
    gset_dom (map_lat_lub m m') = (gset_dom m) ∪ (gset_dom m').
  Proof.
    generalize dependent m'. induction m' using map_ind;
      first (rewrite /map_lat_lub map_fold_empty;
      replace (gset_dom ∅) with (∅: gset string);
        [ set_solver | by apply set_eq ]).
    rewrite /map_lat_lub map_fold_insert;
      [ | apply lat_lub_fold_aux | assumption ].
    apply set_eq. intros s. split.
    + destruct (m !! i)eqn:E'.
      * pose proof (iffLR(elem_of_dom (map_lat_lub m m0) i)).
        rewrite /map_lat_lub in H1.
        destruct H1 as (elt & Helt).
        { rewrite TODO1 IHm'. apply elem_of_dom_2 in E'.
          set_solver. }
        rewrite Helt TODO0.
        intros [Hs|Hs%elem_of_singleton]%elem_of_union.
        --
          rewrite IHm' in Hs.
          apply elem_of_union in Hs as [|]; first by apply elem_of_union_l.
          rewrite TODO0. by apply elem_of_union_r, elem_of_union_l.
        --
          rewrite TODO0.
          by apply elem_of_union_r, elem_of_union_r, elem_of_singleton.
      * intros Hs.
        destruct (map_fold (λ s v' acc, match acc !! s with
              | Some v => map_insert s (v ⊔_l v') acc
              | None => map_insert s v' acc end) m m0 !! i);
        rewrite TODO0 IHm' in Hs; rewrite TODO0;
        apply elem_of_union in Hs as [[Hs|Hs]%elem_of_union|Hs]; set_solver.
    + destruct (map_fold (λ s v' acc, match acc !! s with
            | Some v => map_insert s (v ⊔_l v') acc
            | None => map_insert s v' acc end) m m0 !! i).
      * intros Hs.
        rewrite TODO0 in Hs; rewrite TODO0 IHm';
        apply elem_of_union in Hs as [Hs|[Hs|Hs]%elem_of_union]; set_solver.
      * intros Hs. rewrite TODO0 in Hs. rewrite TODO0 IHm'. set_solver.
  Qed.

  Lemma map_lub_elts (m m': gmap string LogSt) (s: string):
    (∀ v v',
      m !! s = Some v → m' !! s = Some v'
        → (map_lat_lub m m') !! s = Some (latA.(lat_lub) v v'))
    ∧ (∀ (v: LogSt),
        m !! s = Some v → m' !! s = None →
        (map_lat_lub m m') !! s = Some v)
    ∧ (∀ (v: LogSt),
        m !! s = None → m' !! s = Some v →
        (map_lat_lub m m') !! s = Some v)
    ∧ (m !! s = None → m' !! s = None → (map_lat_lub m m') !! s = None).
  Proof.
    generalize dependent s;
    generalize dependent m'; induction m' using map_ind;
      first (intros s; split; first inversion 2;
      intros; by rewrite/map_lat_lub map_fold_empty).
    rewrite /map_lat_lub map_fold_insert;
      [ | apply lat_lub_fold_aux | assumption ].
    set IHSS := λ e, proj1 (IHm' e).
    set IHSN := λ e, proj1(proj2 (IHm' e)).
    set IHNS := λ e, proj1(proj2(proj2 (IHm' e))).
    set IHNN := λ e, proj2(proj2(proj2 (IHm' e))).
    intros s; repeat split.
    * intros v v' Hms Hm0's.
      destruct(decide(i = s))as[-> | ].
      - rewrite (IHSN s v); try done.
        rewrite lookup_insert. by rewrite lookup_insert in Hm0's; simplify_eq/=.
      - destruct(m !! i)as[l|]eqn:E.
        + rewrite (IHSN i l E H0) lookup_insert_ne; last done.
          rewrite lookup_insert_ne in Hm0's; last done.
          by apply (IHSS s).
        + rewrite lookup_insert_ne in Hm0's; last done.
          pose proof (IHm' s)as [IHm'1 IHm'2].
          rewrite (IHNN _ E H0)
            lookup_insert_ne; last done.
          by apply IHSS.
    * intros v Hms Hm0's.
      destruct(decide(i = s))as[-> | ].
      - rewrite (IHSN s v); try done.
        rewrite lookup_insert. by rewrite lookup_insert in Hm0's; simplify_eq/=.
      - destruct(m !! i)as[l|]eqn:E.
        + rewrite (IHSN i l E H0) lookup_insert_ne; last done.
          rewrite lookup_insert_ne in Hm0's; last done.
          by apply IHSN.
        + rewrite lookup_insert_ne in Hm0's; last done.
          rewrite (IHNN _ E H0) lookup_insert_ne; last done.
          by apply IHSN.
    * intros v Hms Hm0s.
      destruct(decide(i = s))as[-> | ].
      - rewrite (IHNN _ Hms H0)lookup_insert.
        by rewrite lookup_insert in Hm0s.
      - destruct(m !! i)as[l|]eqn:E.
        + rewrite lookup_insert_ne in Hm0s; last done.
          rewrite (IHSN i _ E H0) lookup_insert_ne; last done.
          by apply IHNS.
        + rewrite lookup_insert_ne in Hm0s; last done.
          rewrite (IHNN i E H0) lookup_insert_ne; last done.
          by apply IHNS.
    * intros Hms Hm0's.
      destruct(decide(i = s))as[-> | ].
      - by rewrite lookup_insert in Hm0's; simplify_eq/=.
      - destruct(m !! i)as[l|]eqn:E.
        + rewrite (IHSN i _ E H0) lookup_insert_ne; last done.
          apply IHNN; try done.
          by rewrite lookup_insert_ne in Hm0's.
        + rewrite lookup_insert_ne in Hm0's; last done.
          rewrite (IHNN _ E H0) lookup_insert_ne; last done.
          by apply IHNN.
  Qed.

  Lemma map_lub_elt_None_None (m m': gmap string LogSt) (s: string):
    m !! s = None → m' !! s = None → (map_lat_lub m m') !! s = None.
  Proof.
    destruct (map_lub_elts m m' s) as (_&_&_&HNN). intros. by apply HNN. Qed.

  Lemma map_lub_elt_None_Some (m m': gmap string LogSt) (s: string)
    (v: LogSt):
    m' !! s = Some v → m !! s = None →
    (map_lat_lub m m') !! s = Some v.
  Proof.
    destruct (map_lub_elts m m' s) as (_&_&HNS&_). intros. by apply HNS. Qed.

  Lemma map_lub_elt_Some_None (m m': gmap string LogSt) (s: string)
    (v: LogSt):
    m !! s = Some v → m' !! s = None →
    (map_lat_lub m m') !! s = Some v.
  Proof.
    destruct (map_lub_elts m m' s) as (_&HSN&_&_). intros. by apply HSN. Qed.

  Lemma map_lub_elt_Some_Some {m m': gmap string LogSt}{s: string}
    {v v': LogSt}:
    m !! s = Some v → m' !! s = Some v' →
    (map_lat_lub m m') !! s = Some (v ⊔_l v').
  Proof.
    destruct (map_lub_elts m m' s) as (HSS&_&_&_). intros. by apply HSS. Qed.

  Global Instance map_lattice: Lattice (gmap string LogSt).
  Proof.
    refine {|
      lat_le := map_lat_le;
      lat_po := map_lat_le_po;
      lat_lub := map_lat_lub;
    |}.
    intros m m'. repeat split.
    - intros s v Hms.
      destruct(m' !! s) as [v' | ] eqn:Hm's.
      + exists (latA.(lat_lub) v v').
        rewrite (map_lub_elt_Some_Some Hms Hm's).
        split; first trivial.
        by apply lat_lub_le_l.
      + exists v. by rewrite (map_lub_elt_Some_None m m' s v Hms Hm's).
    - intros s v' Hm's.
      destruct (m !! s) as [ v | ] eqn:Hms.
      + exists (latA.(lat_lub) v v').
        rewrite (map_lub_elt_Some_Some Hms Hm's).
        split; first trivial. by apply lat_lub_le_r.
      + exists v'. by rewrite (map_lub_elt_None_Some _ _ _ _ Hm's Hms).
    - intros m'' Hle Hle' s vlub Hlubs.
      destruct (m !! s) as [v|]eqn:Hms; destruct (m' !! s) as [v'|]eqn:Hm's.
      + pose proof (Hle s v Hms) as (v'' & Hv'' & Hle'').
        pose proof (Hle' s v' Hm's) as (v''_bis & Hv''_bis & Hle''_bis).
        assert(v''_bis = v'') as ->. { by simplify_eq. }
        exists v''. split; first trivial.
        rewrite (map_lub_elt_Some_Some Hms Hm's) in Hlubs.
        simplify_eq. by apply lat_lub_le.
      + pose proof (Hle s v Hms) as (v'' & Hv'' & Hle'').
        exists v''. split; first trivial.
        rewrite (map_lub_elt_Some_None _ _ _ _ Hms Hm's) in Hlubs.
        by simplify_eq.
      + pose proof (Hle' s v' Hm's) as (v'' & Hv'' & Hle'').
        exists v''. split; first trivial.
        rewrite (map_lub_elt_None_Some _ _ _ _ Hm's Hms) in Hlubs.
        by simplify_eq.
      + by rewrite (map_lub_elt_None_None _ _ _ Hms Hm's) in Hlubs.
  Defined.

  Global Instance map_op_eqdec: EqDecision mapOp.
  Proof. apply prod_eq_dec. Defined.

  Global Instance map_op_countable: Countable mapOp.
  Proof. apply prod_countable. Qed.

  Definition map_denot_def
    (s: gset (Event mapOp)) (st: mapSt) : Prop :=
    gset_dom st = gset_map (λ ev: Event mapOp, ev.(EV_Op).1) s
    ∧ (∀ (str: string) (v: LogSt), st !! str = Some v →
      @crdt_denot LogOp LogSt timestamp_time eqdec_logop countable_logop
      p.(StLib_Denot)
      (gset_map
          (λ e, {|EV_Op := e.(EV_Op).2;
                  EV_Orig := e.(EV_Orig);
                  EV_Time := e.(EV_Time) |})
        (filter (λ ev, ev.(EV_Op).1 = str) s)) v).

  Global Instance map_denot_fun : Rel2__Fun map_denot_def.
  Proof.
    constructor. intros s m m' (Hdom&Helts)(Hdom'&Helts').
    apply map_eq. intros u.
    destruct (m !! u)as[v|]eqn:Hms; destruct (m' !! u)as[v'|]eqn:Hm's.
    - pose proof (Helts u v Hms) as A. pose proof (Helts' u v' Hm's) as B.
      rewrite Hms Hm's. f_equal.
      exact (p.(StLib_Denot).(crdt_denot_fun).(rel2_fun)A B).
    - exfalso. rewrite -Hdom in Hdom'.
      pose proof (map_dom_Some _ _ _ Hms). apply (map_dom_None _ _ Hm's).
      by rewrite Hdom'.
    - exfalso. rewrite -Hdom in Hdom'.
      pose proof (map_dom_Some _ _ _ Hm's). apply (map_dom_None _ _ Hms).
      by rewrite -Hdom'.
    - by rewrite Hms Hm's.
  Qed.

  Global Instance map_denot: CrdtDenot mapOp mapSt :=
    {| crdt_denot := map_denot_def |}.

  Definition map_event (e: Event mapOp) : Event LogOp :=
    {|EV_Orig := EV_Orig e;
      EV_Op := e.(EV_Op).2;
      EV_Time := EV_Time e;
    |}.

  Context `{PA : !StLib_Params LogOp LogSt}.

  Definition map_mutator (m: mapSt) (e: Event mapOp) (m': mapSt) : Prop :=
    let key: string := e.(EV_Op).1 in
    let val: LogOp := e.(EV_Op).2 in
    gset_dom m' = gset_dom m ∪ {[key]}
    ∧ (∀ k v, k ≠ key → m !! k = Some v → m' !! k = Some v)
    ∧ (∀ (v: LogSt),
        m !! key = Some v →
        ∃ v', PA.(StLib_Model).(st_crdtM_mut) v (map_event e) v'
          ∧ m' !! key = Some v')
    ∧ (m !! key = None →  ∃ (v': LogSt),
        PA.(StLib_Model).(st_crdtM_mut)
          PA.(StLib_Model).(st_crdtM_init_st) (map_event e) v' ∧
        m' !! key = Some v').

  Definition map_event_map :=
    λ e : Event (string * LogOp),
       {|
         EV_Op := (EV_Op e).2;
         EV_Orig := EV_Orig e;
         EV_Time := EV_Time e
       |}.

  Lemma lst_val_map s lst:
    Lst_Validity' lst →
    Lst_Validity'
      (gset_map map_event_map
        (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) lst)).
  Proof.
    destruct 1.
    apply (lst_validity'_valid_event_map). split;
    try intros ??[_?]%elem_of_filter[_?]%elem_of_filter;
    try intros?[_?]%elem_of_filter;
    [ by apply VLst_same_orig_comp'
    | by apply VLst_ext_eqid'
    | by apply VLst_ext_time'
    | by apply VLst_orig'
    | by apply VLst_seqnum_non_O'
    | | by apply VLst_evid_mon'
    | by apply VLst_evid_incl_event'
    | by apply VLst_evid_incl_time_le' ].
    - intros??.
      destruct
        (set_choose_or_empty(hproj i(filter (λ ev, (EV_Op ev).1 = s) lst)));
        [right | by left].
      destruct (compute_maximum_non_empty
        (hproj i (filter (λ ev, (EV_Op ev).1 = s) lst))).
      + intros??[?[_?]%elem_of_filter]%elem_of_filter
          [?[_?]%elem_of_filter]%elem_of_filter.
        apply VLst_same_orig_comp'; [done|done|lia].
      + intros??[?[_?]%elem_of_filter]%elem_of_filter
          [?[_?]%elem_of_filter]%elem_of_filter.
        by apply VLst_ext_time'.
      + destruct H2 as[x Hx]; first set_solver.
        exists x. split; last done.
        apply compute_maximum_correct in Hx as [??]; last first.
        intros??[?[??]%elem_of_filter]%elem_of_filter
          [?[??]%elem_of_filter]%elem_of_filter.
        by apply VLst_ext_time'.
        apply elem_of_filter; set_solver.
  Qed.

  Lemma map_mut_lub_coh:
    ∀ (s1 s2 : event_set mapOp) (st1 st2 st3 : mapSt),
      ⟦ s1 ⟧ ⇝ st1
      → ⟦ s2 ⟧ ⇝ st2
      → Lst_Validity' s1
      → Lst_Validity' s2 → Lst_Validity' (s1 ∪ s2)
      → (∀ i : nat, fil s1 i ⊆ fil s2 i ∨ fil s2 i ⊆ fil s1 i)
      → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    intros s1 s2 st1 st2 st3[Hdom Hden][Hdom' Hden']Hv1 Hv2 Hv3 Hproj <-.
    split; first by rewrite map_lat_lub_dom Hdom Hdom' gset_map_union.
    intros s v Hs.
    set mapped_s1 := gset_map
      (λ e : Event (string * LogOp),
      {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
      (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) s1).
    set mapped_s2 := gset_map
      (λ e : Event (string * LogOp),
      {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
      (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) s2).
    set mapped_s12 := gset_map
      (λ e : Event (string * LogOp),
      {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
      (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) (s1 ∪ s2)).
    destruct (st1 !! s) as [l |] eqn:E;
    destruct (st2 !! s) as [l' |] eqn:E';
    last (exfalso; pose proof (map_lub_elt_None_None st1 st2 s E E');
      by rewrite H0 in Hs).
    - pose proof (map_lub_elt_Some_Some E E').
      replace mapped_s12 with (mapped_s1 ∪ mapped_s2); last set_solver.
      pose proof (Hden s l E) as H1; pose proof (Hden' s l' E') as H2.
      rewrite-/mapped_s1 in H1; rewrite-/mapped_s2 in H2.
      apply (p.(StLib_Model).(st_crdtM_lub_coh)_ _ _ _ _ H1 H2).
      + by apply lst_val_map.
      + by apply lst_val_map.
      + assert((mapped_s1 ∪ mapped_s2) = mapped_s12) as Hseq; first set_solver.
        rewrite Hseq. by apply lst_val_map.
      + rewrite Hs in H0.
        intros i. destruct (Hproj i); [left | right]; set_solver.
      + rewrite(map_lub_elt_Some_Some E E') in Hs. by simplify_eq/=.
    - pose proof (map_lub_elt_Some_None st1 st2 s l E E')as H0.
      replace mapped_s12 with (mapped_s1 ∪ mapped_s2); last set_solver.
      pose proof (Hden s l E) as H1.
      rewrite-/mapped_s1 in H1.
      assert(mapped_s2 = ∅) as ->.
      { apply map_dom_None in E'. set_solver. }
      rewrite Hs in H0. simplify_eq/=.
      replace (mapped_s1 ∪ ∅) with mapped_s1; [assumption | set_solver].
    - pose proof (map_lub_elt_None_Some st1 st2 s l' E' E)as H0.
      replace mapped_s12 with (mapped_s1 ∪ mapped_s2); last set_solver.
      pose proof (Hden' s l' E') as H2.
      rewrite-/mapped_s2 in H2.
      assert(mapped_s1 = ∅) as ->.
      { apply map_dom_None in E. set_solver. }
      rewrite Hs in H0. simplify_eq/=.
      replace (∅ ∪ mapped_s2) with mapped_s2; [assumption | set_solver].
  Qed.

  Lemma map_mut_coh:
    ∀ (s : event_set mapOp) (st st' : mapSt) (ev : Event mapOp),
      ⟦ s ⟧ ⇝ st
      → Lst_Validity s
      → ev ∉ s
      → is_maximum ev (s ∪ {[ev]})
      → map_mutator st ev st' → ⟦ s ∪ {[ev]} ⟧ ⇝ st'.
  Proof.
  Admitted.

  Lemma map_mut_mon (m : mapSt) (e : Event mapOp) (m' : mapSt) :
    map_mutator m e m' → m ≤_l m'.
  Proof.
    intros(Hdom&Hold_v&Hnew_v&Hnew_v')s v Hmsv.
    destruct(decide(s = (EV_Op e).1)) as[-> | ].
    + destruct (Hnew_v _ Hmsv)as(v'&Hmut&Hm'sv').
      exists v'. split; first assumption.
      apply st_crdtM_mut_mon with (map_event e).
      apply Hmut.
    + exists v. split; last done. exact (Hold_v s v n Hmsv).
  Qed.

  Global Instance map_model : StateCrdtModel mapOp mapSt.
  Proof.
    refine {| st_crdtM_lub_coh := map_mut_lub_coh;
              st_crdtM_mut_mon := map_mut_mon;
              st_crdtM_mut_coh := map_mut_coh;
              st_crdtM_mut := map_mutator;
              st_crdtM_init_st := gmap_empty; |}.
    split; [ by apply set_eq | inversion 1 ].
  Defined.



  (** serialization *)
  Definition map_ser : serialization :=
    list_serialization
      (prod_serialization
        string_serialization p.(StLib_CohParams).(StLib_StSerialization)).

  Definition map_op_coh (op: mapOp) (v: val): Prop :=
    ∃(s: string)(lop: LogOp)(vs vop: val),
      op.1 = s ∧ op.2 = lop
      ∧ v = (vs, vop)%V
      ∧ p.(StLib_CohParams).(StLib_Op_Coh) lop vop
      ∧ vs = #s.

  Definition map_st_coh (st: mapSt) (v: val): Prop := is_map v st.

  Lemma map_coh_ser:
    ∀ (st : mapSt) (v : val), map_st_coh st v → Serializable map_ser v.
    Admitted.

  Global Instance map_coh_params : @StLib_Coh_Params mapOp mapSt.
  Proof.
    refine {|
      StLib_StSerialization := map_ser;
      StLib_Op_Coh := map_op_coh;
      StLib_St_Coh := map_st_coh; |}.
    - intros [ol or][ol' or'] v
        (s & lop & vs & vop & Hseq & Hlopeq & Hveq & Hlopcoh & Hvsq)
        (s'& lop'& vs'& vop'& Hseq'& Hlopeq'& Hveq'& Hlopcoh'& Hvsq').
      f_equal; first by simplify_eq/=.
      simplify_eq/=. by apply (p.(StLib_CohParams).(StLib_Op_Coh_Inj)lop lop' vop').
    - intros st st' v (l&->&Hl&H'l)(l'&->&Hl'&H'l').
      assert(l=l') as ->; last reflexivity.
      rewrite Hl in Hl'. by apply inject_inj.
    - exact map_coh_ser.
  Defined.

  Global Instance map_params : StLib_Params mapOp mapSt :=
    {|
      StLib_CohParams := map_coh_params;
      StLib_Denot := map_denot;
      StLib_Model := map_model;
    |}.

End Bloup.

Arguments map_params {_ _ _ _ _ _ _ _ _ _}.

Section MapComp_Proof.
  Context (LogOp : Type) (LogSt : Type).
  Context `{!EqDecision LogOp} `{!Countable LogOp}.
  Context `{!Inject LogSt val}.
  Context `{lat : Lattice LogSt}.
  Context `{a: anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{PA : !StLib_Params LogOp LogSt}.

  Lemma map_init_st_fn_spec :
    ⊢ @init_st_fn_spec (mapOp LogOp) (mapSt LogSt)_ _ _ _ _ _ _ _ map_comb_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /map_comb_init_st.
    wp_pures. wp_apply wp_map_empty; first trivial.
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro.
    by rewrite/StLib_St_Coh/StLib_CohParams/map_params/map_coh_params
      /map_st_coh/st_crdtM_init_st/StLib_Model/map_model.
  Qed.

  Lemma map_mutator_st_spec mut_fn init_fn :
    @init_st_fn_spec LogOp LogSt _ _ _ _ _ _ _ PA init_fn -∗
    (** TODO: Init !!! *)
    @mutator_spec LogOp LogSt _ _ _ _ _ _ _ PA mut_fn -∗
    @mutator_spec  (mapOp LogOp) (mapSt LogSt) _ _ _ _ _ _ _ map_params
      (λ: "i" "gs" "op", map_comb_mutator init_fn mut_fn "i" "gs" "op").
  Proof.
  Admitted.

  Lemma map_merge_st_spec merge_fn :
    @merge_spec LogOp LogSt _ _ _ _ _ _ _ PA merge_fn -∗
    @merge_spec _ _ _ _ _ _ _ _ _ map_params
    (λ: "st1" "st2", map_comb_merge merge_fn "st1" "st2").
  Proof.
  Admitted.

  Lemma map_crdt_fun_spec cA :
    @crdt_fun_spec LogOp LogSt _ _ _ _ _ _ _ PA cA -∗
    @crdt_fun_spec _ _ _ _ _ _ _ _ _ map_params
    (λ: <>, map_comb_crdt cA #()).
  Proof.
    iIntros "#Hfun_spec"(?)"!>%φ _ Hφ".
    do 2 wp_lam.
    wp_apply "Hfun_spec"; first trivial.
    iIntros (v_triplet) "(%v_init & %v_mut & %v_merge & -> & #Hinit_spec & Hmut_spec & Hmerge_spec)".
    do 14 wp_pure _. wp_let. wp_pure _. wp_let. wp_pures.
    iApply "Hφ".
    iExists _, _, _.
    iSplit; first (iPureIntro; reflexivity).
    repeat iSplit.
    - by iApply map_init_st_fn_spec.
    - by iApply map_mutator_st_spec.
    - by iApply map_merge_st_spec.
  Qed.

  Lemma map_init_spec `{!StLib_Res (@mapOp LogOp)} cA :
    @crdt_fun_spec LogOp LogSt _ _ _ _ _ _ _ PA cA -∗
    @init_spec _ _ _ _ _ _ _ _ _ map_params _
      (statelib_init
        (string_map_ser
            (PA.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_ser))
        (string_map_deser
            (PA.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_deser))) -∗
    @init_spec_for_specific_crdt _ _ _ _ _ _ _ _
      map_params.(StLib_Denot) map_params.(StLib_CohParams) _
      (λ: "addrs" "rid",
         map_comb_init
          (PA.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_ser)
          (PA.(StLib_CohParams).(StLib_StSerialization).(s_serializer)).(s_deser)
          cA "addrs" "rid").
  Proof.
  Admitted.

End MapComp_Proof.


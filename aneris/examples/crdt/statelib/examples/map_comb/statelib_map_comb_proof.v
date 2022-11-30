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

  Context `{PA : !StLib_Params LogOp LogSt}.

  Definition map_denot_def
    (s: gset (Event mapOp)) (st: mapSt) : Prop :=
    gset_dom st = gset_map (λ ev: Event mapOp, ev.(EV_Op).1) s
    ∧ (∀ (str: string) (v: LogSt), st !! str = Some v →
      @crdt_denot LogOp LogSt timestamp_time eqdec_logop countable_logop
      PA.(StLib_Denot)
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
      exact (PA.(StLib_Denot).(crdt_denot_fun).(rel2_fun)A B).
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

  Definition map_mutator (m: mapSt) (e: Event mapOp) (m': mapSt) : Prop :=
    let key: string := e.(EV_Op).1 in
    let val: LogOp := e.(EV_Op).2 in
    (∀ k v, k ≠ key → m !! k = Some v ↔ m' !! k = Some v)
    ∧ ∃ (v': LogSt),
        m' !! key = Some v'
        ∧ st_crdtM_mut (default st_crdtM_init_st (m !! key)) (map_event e) v'.

  Lemma map_mutator_dom {m m': mapSt}{e: Event mapOp}:
    map_mutator m e m' → gset_dom m' = gset_dom m ∪ {[e.(EV_Op).1]}.
  Proof.
    intros(Hold&v'&Hm'k&Hnew).
    apply set_eq; intros x; split;
    destruct (decide(x = e.(EV_Op).1))as[-> | A];
      [ by (intros _; apply elem_of_union_r, elem_of_singleton)
      | by intros[v?]%map_dom_Some_2;
        apply elem_of_union_l, map_dom_Some with v, Hold
      | intros _; by apply map_dom_Some with v'
      |intros[[v?]%map_dom_Some_2| ->%elem_of_singleton]%elem_of_union;
        [by apply map_dom_Some with v, Hold
        |by apply map_dom_Some with v'] ].
  Qed.

  Lemma lst_val_map s lst:
    Lst_Validity' lst →
    Lst_Validity'
      (gset_map map_event
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

  Lemma map_mut_coh:
    ∀ (s : event_set mapOp) (st st' : mapSt) (ev : Event mapOp),
      ⟦ s ⟧ ⇝ st
      → Lst_Validity' s
      → ev ∉ s
      → is_maximum ev (s ∪ {[ev]})
      → map_mutator st ev st' → ⟦ s ∪ {[ev]} ⟧ ⇝ st'.
  Proof.
    intros s m m' ev [Hdom Hden] Hv Hnin Hmax Hmut.
    split; first (rewrite (map_mutator_dom Hmut); set_solver).
    destruct Hmut as(Hold&v&Hm'k&Hnew).
    intros x v' Hm'x.
    set sx :=
      gset_map map_event (filter (λ ev0, (EV_Op ev0).1 = (EV_Op ev).1) s).
    assert(gset_map map_event
        (filter (λ ev0, (EV_Op ev0).1 = (EV_Op ev).1) (s ∪ {[ev]}))
      = sx ∪ {[map_event ev]}) as Heq; first set_solver.
    destruct(decide(x = ev.(EV_Op).1))as[ -> | Hneq].
    - simplify_eq/=. rewrite-/map_event Heq.
      destruct (m !! ev.(EV_Op).1)as[l|]eqn:E.
      + pose proof (Hden (EV_Op ev).1) l E as H0; rewrite-/sx in H0.
        apply (st_crdtM_mut_coh sx _ _ _ H0);
          [ by apply lst_val_map | | | by simplify_eq ].
          intros (x&Hx_map_eq&[]%elem_of_filter)%gset_map_correct2.
          assert(Lst_Validity' (s ∪ {[ev]})) as Hv'.
          { split.
            - destruct Hmax as [_ Hmax].
              intros??[| ->%elem_of_singleton]%elem_of_union[| ->%elem_of_singleton]%elem_of_union?.
              + by apply (VLst_same_orig_comp' s Hv e e').
              + left. apply Hmax; set_solver.
              + do 2 right. apply Hmax; set_solver.
              + by right; left.
            - admit.
            - destruct Hmax as [_ Hmax].
              intros??[| ->%elem_of_singleton]%elem_of_union[| ->%elem_of_singleton]%elem_of_union?.
              + by apply (VLst_ext_time' s Hv).
              + exfalso; epose proof Hmax ev0 _ _.
                rewrite H4 in H5. by apply (ts_lt_irreflexive (EV_Time ev)).
              + exfalso; epose proof Hmax ev' _ _.
                rewrite H4 in H5. by apply (ts_lt_irreflexive (EV_Time ev')).
              + reflexivity.
            - intros?[| ->%elem_of_singleton]%elem_of_union;
                [|inversion Hx_map_eq; rewrite H5];
                by apply (VLst_orig' s Hv).
            - intros?[| ->%elem_of_singleton]%elem_of_union;
                first by apply (VLst_seqnum_non_O' s Hv).
              admit.
            - admit.
            - admit.
            - admit.
            - admit.
            Unshelve.
            all: set_solver. }
          assert(x = ev) as ->; last done.
          apply (VLst_ext_time' _ Hv');
            [ by apply elem_of_union_l
            | by apply elem_of_union_r,elem_of_singleton
            | by inversion Hx_map_eq ].
        * split; first by apply elem_of_union_r, elem_of_singleton.
          intros t [(p&->&[]%elem_of_filter)%gset_map_correct2| ->%elem_of_singleton]%elem_of_union Ht_neq;
            last done.
          destruct Hmax as [_ B].
          by epose proof (B p _ _).
          Unshelve.
          by apply elem_of_union_l.
          by intros->.
      + assert(sx = ∅) as ->.
        { simplify_eq/=. apply map_dom_None in E. rewrite Hdom in E.
          apply set_eq; intros ?; split; [ | inversion 1 ].
          intros (?&->&[]%elem_of_filter)%gset_map_correct2.
          destruct E. set_solver. }
        simplify_eq/=.
        apply (st_crdtM_mut_coh ∅) with st_crdtM_init_st; try done;
          [exact st_crdtM_init_st_coh | split; try by intros; try by left | ].
        split; first by apply elem_of_union_r, elem_of_singleton.
        by intros?[?| ->%elem_of_singleton]%elem_of_union.
  Admitted.

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
      apply (PA.(StLib_Model).(st_crdtM_lub_coh)_ _ _ _ _ H1 H2).
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

  Lemma map_mut_mon (m : mapSt) (e : Event mapOp) (m' : mapSt) :
    map_mutator m e m' → m ≤_l m'.
  Proof.
    intros (Hdom&v'&Hm'k&Hmk)s v Hms.
    destruct(decide(s = (EV_Op e).1)) as[-> | ];
      last (exists v; split; last done; by apply Hdom).
    exists v'. split; first assumption.
    apply st_crdtM_mut_mon with (map_event e).
    by rewrite Hms in Hmk.
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
        string_serialization PA.(StLib_CohParams).(StLib_StSerialization)).

  Definition map_op_coh (op: mapOp) (v: val): Prop :=
    ∃(s: string)(lop: LogOp)(vs vop: val),
      op.1 = s ∧ op.2 = lop
      ∧ v = (vs, vop)%V
      ∧ PA.(StLib_CohParams).(StLib_Op_Coh) lop vop
      ∧ vs = #s.

  Definition map_st_coh_v_log (v: val) (m: gmap string val) (st: mapSt) :=
      is_map v m ∧
      gset_dom m = gset_dom st ∧
      ∀ k vs w, m !! k = Some w → st !! k = Some vs → StLib_St_Coh vs w.
  
  Definition map_st_coh :=
    λ (st : mapSt) v,
      ∃ (m : gmap string val), map_st_coh_v_log v m st.

  Lemma map_coh_ser:
    ∀ (st : mapSt) (v : val), map_st_coh st v →
      Serializable map_ser v.
  Proof.
    intros m v (x&H1&H2&Hnodup).
    (*exists x.*)
    Admitted.

  Lemma map_coh_inj:
    ∀ (o1 o2 : mapSt) (v : val), map_st_coh o1 v → map_st_coh o2 v → o1 = o2.
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
      simplify_eq/=. by apply (PA.(StLib_CohParams).(StLib_Op_Coh_Inj)lop lop' vop').
    - exact map_coh_inj.
    - exact map_coh_ser.
  Defined.

  Global Instance map_params : StLib_Params mapOp mapSt :=
    {|
      StLib_CohParams := map_coh_params;
      StLib_Denot := map_denot;
      StLib_Model := map_model;
    |}.

  Context `{a: anerisG M Σ}.

  Lemma map_init_st_fn_spec :
    ⊢ @init_st_fn_spec mapOp mapSt _ _ _ _ _ _ _ _ map_comb_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /map_comb_init_st.
    wp_pures. wp_apply wp_map_empty; first trivial.
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro.
    exists gmap_empty. repeat split; try done.
    rewrite/st_crdtM_init_st/StLib_Model/map_params/map_model. set_solver.
  Qed.

  Lemma map_mutator_st_spec mut_fn init_fn :
    @init_st_fn_spec LogOp LogSt _ _ _ _ _ _ _ PA init_fn -∗
    (** TODO: Init !!! *)
    @mutator_spec LogOp LogSt _ _ _ _ _ _ _ PA mut_fn -∗
    @mutator_spec  mapOp mapSt _ _ _ _ _ _ _ map_params
      (λ: "i" "gs" "op", map_comb_mutator init_fn mut_fn "i" "gs" "op").
  Proof.
    iIntros "#Hinit #Hmut_spec" (addr id st_v op_v s ev_log op_log st_log)
      "!> %φ (%Hop_coh&%Hst_coh&%Hden&%Hnin&%Hop&%Horig&%Hmax&%Hevents_ext&%Hsame_orig_comp) Hφ".
    destruct Hop_coh as (_&_&_&vop&<-&<-&->&Hlop_coh&->).
    destruct Hst_coh as (m&Hm_ismap&Hm_dom&Hm_elts).
    destruct op_log as [op_log_key op_log_op].
    iSimplifyEq.
    destruct(st_log !! (EV_Op ev_log).1)as[l|]eqn:E.
    - do 2 (wp_lam; wp_pures).
      wp_apply (wp_map_lookup (K := string) (V := val)); first done.
      iIntros(l_v) "%Hl_v". rewrite Hop/= in E.
      pose proof (map_dom_Some _ _ _ E) as HE. rewrite -Hm_dom in HE.
      destruct (map_dom_Some_2 _ _ HE) as (l'&F);
      rewrite F in Hl_v; rewrite Hl_v.
      wp_pures.
      wp_apply "Hmut_spec".
      { iPureIntro. repeat split;
          first (replace op_log_op with (EV_Op (map_event ev_log)) in Hlop_coh;
            [done | simpl; by rewrite Hop ]).
        1: exact (Hm_elts op_log_key l l' F E).
        3: reflexivity. 3: by apply elem_of_union_r, elem_of_singleton.
        - destruct Hden as (Hden_dom&Hden_elts).
          exact (Hden_elts op_log_key l E).
        - intros (e&He&[_ He_in]%elem_of_filter)%gset_map_correct2.
          by assert(e = ev_log) as ->;
            first (apply (Hevents_ext e ev_log);
              [set_solver | set_solver | by inversion He]).
        - apply elem_of_union in H0 as [(e&He&He_in)%gset_map_correct2| ->%elem_of_singleton]; last done.
          replace(time(map_event ev_log)) with(time ev_log); last done.
          replace(time t) with(time e); last by inversion He.
          destruct Hmax as [_ Hmax];
          by epose proof (Hmax e _ _)as H0%TM_lt_TM_le.
          Unshelve.
          set_solver.
          intros ->; by inversion He.
        - apply elem_of_union in H0 as [(e&He&He_in)%gset_map_correct2| ->%elem_of_singleton]; last done.
          replace(time(map_event ev_log)) with(time ev_log); last done.
          replace(time t) with(time e); last by inversion He.
          destruct Hmax as [_ Hmax].
          epose proof (Hmax e _ _)as H0; set_solver.
          Unshelve.
          set_solver.
          intros ->; by inversion He.
        - intros e e'
            [(b&?&?)%gset_map_correct2| ->%elem_of_singleton]%elem_of_union
            [(b'&?&?)%gset_map_correct2| ->%elem_of_singleton]%elem_of_union;
            last reflexivity.
          + intros ?. epose proof (Hevents_ext b b' _ _ _).
            by simplify_eq.
            Unshelve.
            3: replace (time b) with(time e); last (by simplify_eq/=);
              by replace (time b') with(time e'); last by simplify_eq/=.
            all: set_solver.
          + intros Ht. assert(b = ev_log) as ->;
              first apply Hevents_ext; set_solver.
          + intros Ht. assert(b' = ev_log) as ->;
              first apply Hevents_ext; set_solver.
        - intros e e'
            [(b&?&?)%gset_map_correct2| ->%elem_of_singleton]%elem_of_union
            [(b'&?&?)%gset_map_correct2| ->%elem_of_singleton]%elem_of_union;
            last by right; left.
          + replace(time e)with(time b); last by inversion H0.
            replace(time e')with(time b'); last by inversion H2.
            intros?; by epose proof (Hsame_orig_comp b b' _ _ _).
            Unshelve.
            3: by simplify_eq/=.
            all: set_solver.
          + replace(time e)with(time b); last by inversion H0.
            intros?; by epose proof (Hsame_orig_comp b ev_log _ _ _).
            Unshelve.
            3: by simplify_eq/=.
            all: set_solver.
          + replace(time e')with(time b'); last by inversion H0.
            intros?; by epose proof (Hsame_orig_comp ev_log b' _ _ _).
            Unshelve.
            3: by simplify_eq/=.
            all: set_solver. }
      iIntros (st'_v (st'_log&Hst'_coh&Hst'_mut)).
      wp_pures.
      wp_apply (wp_map_insert (K := string) (V := val) _ op_log_key); first done.
      iIntros(d Hd).
      iApply "Hφ".
      iPureIntro.
      exists (<[op_log_key:=st'_log]> st_log); split.
      + exists (<[op_log_key:=st'_v]> m); repeat split; first done.
        { apply set_eq; intro x; destruct (decide(x = op_log_key))as[->|Hneq];
          split; intros Hin;
            [ apply map_dom_Some with st'_log; by rewrite lookup_insert
            | apply map_dom_Some with st'_v; by rewrite lookup_insert
            |
            | ].
          - destruct (st_log !! x)eqn:G.
            * apply map_dom_Some with l0.
              by rewrite lookup_insert_ne; last done.
            * exfalso.
              apply map_dom_Some_2 in Hin as(v&Hmx).
              rewrite lookup_insert_ne in Hmx; last done.
              pose proof (map_dom_Some m x v Hmx) as Hx.
              rewrite Hm_dom in Hx.
              apply map_dom_Some_2 in Hx as(v'&Hstx).
              by rewrite Hstx in G.
          - destruct (m !! x)as[l0| ]eqn:G.
            * apply map_dom_Some with l0.
              by rewrite lookup_insert_ne; last done.
            * exfalso.
              apply map_dom_Some_2 in Hin as(v&Hmx).
              rewrite lookup_insert_ne in Hmx; last done.
              pose proof (map_dom_Some st_log x v Hmx) as Hx.
              rewrite -Hm_dom in Hx.
              apply map_dom_Some_2 in Hx as(v'&Hstx).
              by rewrite Hstx in G. }
        intros x vs w Hmx Hstx.
        destruct(decide(x = op_log_key)) as [-> | Hneq].
        * rewrite lookup_insert in Hmx; rewrite lookup_insert in Hstx.
          by simplify_eq/=.
        * rewrite lookup_insert_ne in Hmx; last done.
          rewrite lookup_insert_ne in Hstx; last done.
          by apply Hm_elts with x.
      + split;
          last (exists st'_log; split;
            [ by rewrite Hop/= lookup_insert | by rewrite Hop/= E/= ]).
        intros???. split; intros?;
          last (rewrite lookup_insert_ne in H1; try done;
            by rewrite Hop in H0).
        rewrite Hop/= in H0.
        by rewrite lookup_insert_ne; last done.
    - do 2 (wp_lam; wp_pures).
      wp_apply (wp_map_lookup (K := string) (V := val)); first done.
      iIntros(l_v) "%Hl_v". rewrite Hop/= in E.
      assert(F: m !! op_log_key = None).
      { apply map_dom_None in E. rewrite -Hm_dom in E.
        by apply not_elem_of_dom. }
      rewrite F in Hl_v; rewrite Hl_v.
      wp_pures.
      wp_apply "Hinit"; first trivial.
      iIntros(vinit Hinit_st_coh).
      wp_apply "Hmut_spec".
      { iPureIntro. repeat split; try done;
          first (replace op_log_op with (EV_Op (map_event ev_log)) in Hlop_coh;
            [done | simpl; by rewrite Hop ]).
        3: reflexivity.
        3: by apply elem_of_union_r, elem_of_singleton.
        - apply st_crdtM_init_st_coh.
        - by intros?.
        - exfalso; set_solver.
        - exfalso; set_solver.
        - intros?????. set_solver.
        - intros?????. set_solver. }
      iIntros (st'_v (st'_log&Hst'_coh&Hst'_mut)).
      wp_pures.
      wp_apply (wp_map_insert (K := string) (V := val) _ op_log_key); first done.
      iIntros(d Hd).
      iApply "Hφ".
      iPureIntro.
      exists (<[op_log_key:=st'_log]> st_log); split.
      + exists (<[op_log_key:=st'_v]> m); repeat split; first done.
        { apply set_eq; intro x; destruct (decide(x = op_log_key))as[->|Hneq];
          split; intros Hin;
            [ apply map_dom_Some with st'_log; by rewrite lookup_insert
            | apply map_dom_Some with st'_v; by rewrite lookup_insert
            |
            | ].
          - destruct (st_log !! x)eqn:G.
            * apply map_dom_Some with l.
              by rewrite lookup_insert_ne; last done.
            * exfalso.
              apply map_dom_Some_2 in Hin as(v&Hmx).
              rewrite lookup_insert_ne in Hmx; last done.
              pose proof (map_dom_Some m x v Hmx) as Hx.
              rewrite Hm_dom in Hx.
              apply map_dom_Some_2 in Hx as(v'&Hstx).
              by rewrite Hstx in G.
          - destruct (m !! x)as[l| ]eqn:G.
            * apply map_dom_Some with l.
              by rewrite lookup_insert_ne; last done.
            * exfalso.
              apply map_dom_Some_2 in Hin as(v&Hmx).
              rewrite lookup_insert_ne in Hmx; last done.
              pose proof (map_dom_Some st_log x v Hmx) as Hx.
              rewrite -Hm_dom in Hx.
              apply map_dom_Some_2 in Hx as(v'&Hstx).
              by rewrite Hstx in G. }
        intros x vs w Hmx Hstx.
        destruct(decide(x = op_log_key)) as [-> | Hneq].
        * rewrite lookup_insert in Hmx; rewrite lookup_insert in Hstx.
          by simplify_eq/=.
        * rewrite lookup_insert_ne in Hmx; last done.
          rewrite lookup_insert_ne in Hstx; last done.
          by apply Hm_elts with x.
      + split;
          last (exists st'_log; split;
            [ by rewrite Hop/= lookup_insert | by rewrite Hop/= E/= ]).
        intros???. split; intros?;
          last (rewrite lookup_insert_ne in H1; try done;
            by rewrite Hop in H0).
        rewrite Hop/= in H0.
        by rewrite lookup_insert_ne; last done.
  Qed.

  Lemma bloup (addr : socket_address) merge_fn
    (st_v_v st'_v_v: val) (st_v_log st'_v_log: gmap string val)
    (st_log st'_log: mapSt)
    (s s': event_set mapOp) (Hsden: ⟦ s ⟧ ⇝ st_log) (Hs'den: ⟦ s' ⟧ ⇝ st'_log)
    (key : string)
    (acc_v : val) (* Current result *)
    (Xacc : gset string) (* keys seen so far (ie. in previous iterations) *)
    (Hevents_ext : events_ext s)
    (Hsame_orig_comp : event_set_same_orig_comparable s)
    (Hevents_ext' : events_ext s')
    (Hsame_orig_comp' : event_set_same_orig_comparable s') :
    let lub_log: mapSt := map_lat_lub st_log st'_log in
    let P := λ (X: gset string) (a: val),
      ∃ (m: gmap string val),
      gset_dom m = X
      ∧ is_map a m
      ∧ (∀ (s: string),
        s ∈ X →
        ∃ (vs: val) (es: LogSt),
          m !! s = Some vs
          ∧ lub_log !! s = Some es
          ∧ StLib_St_Coh es vs) in
    ⌜ map_st_coh_v_log st_v_v st_v_log st_log ⌝ -∗
    ⌜ map_st_coh_v_log st'_v_v st'_v_log st'_log ⌝ -∗
    @merge_spec LogOp LogSt _ _ _ _ _ _ _ PA merge_fn -∗
    {{{ ⌜P Xacc acc_v⌝ ∗ ⌜key ∈ (gset_dom st_log) ∪ (gset_dom st'_log)⌝ }}}
    (λ: "m" "k",
      match: map_lookup "k" st_v_v with
        InjL <> =>
          match: map_lookup "k" st'_v_v with
            InjL <> => assert: #false
          | InjR "v1" => map_code.map_insert "k" "v1" "m"
          end
      | InjR "v0" =>
        match: map_lookup "k" st'_v_v with
          InjL <> => map_code.map_insert "k" "v0" "m"
        | InjR "v1" => map_code.map_insert "k" (merge_fn "v0" "v1") "m"
        end
      end)%V acc_v $ key @[ip_of_address addr]
  {{{ (res_v : val),  RET res_v; ⌜P (Xacc ∪ {[key]}) res_v⌝ ∗ ⌜key ∈ gset_dom (lub_log)⌝ }}}.
  Proof.
    intros lub_log P.
    iIntros((Hst_ismap&Hst_dom&Hst_elts)(Hst'_ismap&Hst'_dom&Hst'_elts))
      "#Hmerge%φ!>[(%m&%Hm_dom&%Hm_ismap&%Hm_elts) %Hkey] Hφ".
    wp_lam; wp_let.
    wp_apply (wp_map_lookup (K := string) (V := val)); first done.
    destruct(st_v_log !! key)as[l|]eqn:E.
    - destruct (st_log !! key)as[l_log|]eqn:E';
        last by (apply map_dom_Some in E; apply map_dom_None in E';
          by rewrite -Hst_dom in E').
      iIntros(v->).
      wp_pures.
      wp_apply (wp_map_lookup (K := string) (V := val)); first done.
      destruct(st'_v_log !! key)as[l'|]eqn:F.
      + destruct (st'_log !! key)as[l'_log|]eqn:F';
          last by ( apply map_dom_Some in F; apply map_dom_None in F';
            rewrite-Hst'_dom in F').
        iIntros(v'->). wp_pures.
        wp_bind(merge_fn _ _)%E.
        wp_apply "Hmerge".
        { iPureIntro.
          destruct Hsden as[Hs_dom Hs_den]; destruct Hs'den as[Hs'_dom Hs'_den].
          pose proof(Hst_elts key l_log l E E').
          pose proof(Hst'_elts key l'_log l' F F').
          pose proof (Hs_den key l_log E').
          pose proof (Hs'_den key l'_log F').
          repeat split; try done.
          all: (intros e1 e2 (e&He&[_ Hein]%elem_of_filter)%gset_map_correct2
                      (e'&He'&[_ He'in]%elem_of_filter)%gset_map_correct2?;
            inversion He; inversion He'; simplify_eq/=).
          1: by rewrite(Hevents_ext e e').
          2: by rewrite(Hevents_ext' e e').
          1: by apply(Hsame_orig_comp e e').
          1: by apply(Hsame_orig_comp' e e'). }
        iIntros(loc_lub_val (loc_lub_log&Hloc_lub_coh&Hloc_lub_eq)).
        wp_apply (wp_map_insert (K := string) (V := val) _ key ); first done.
        iIntros(st''_v Hst'').
        iApply"Hφ".
        iPureIntro.
        split; last (rewrite map_lat_lub_dom; apply elem_of_union_l;
            rewrite-Hst_dom; by apply map_dom_Some in E).
        exists (<[key:=loc_lub_val]> m); repeat split; try done.
        * rewrite-Hm_dom.
          replace (gset_dom(<[key:=loc_lub_val]> m))with(dom(<[key:=loc_lub_val]> m)); last set_solver. 
          replace (gset_dom m) with (dom m); last set_solver. 
          set_solver.
        * intros x Hxin; destruct(decide(x = key))as[->|Hneq].
          ++pose proof (map_lub_elt_Some_Some E' F') as Hsome.
            exists loc_lub_val, (l_log ⊔_l l'_log).
            repeat split; [ by rewrite lookup_insert | done | ].
            replace(l_log ⊔_l l'_log)with loc_lub_log.
            exact Hloc_lub_coh.
          ++apply elem_of_union in Hxin as [Hx_in| ->%elem_of_singleton]; last (exfalso; by set_solver).
            rewrite lookup_insert_ne; last done.
            by apply Hm_elts.
    + iIntros(v'->). wp_pures.
      wp_apply (wp_map_insert (K := string) (V := val) _ key ); first done.
      iIntros(st''_v Hst'').
      iApply"Hφ".
      iPureIntro.
      split; last(by rewrite map_lat_lub_dom).
      exists (<[key:=l]> m); repeat split; [| done |].
      * rewrite-Hm_dom.
        replace (gset_dom(<[key:=l]> m))with(dom(<[key:=l]> m)); last set_solver. 
        replace (gset_dom m) with (dom m); last set_solver. 
        set_solver.
      * intros x Hxin.
        destruct(decide(x = key))as[->| J].
        --exists l, l_log; repeat split;
            [ by rewrite lookup_insert | | by apply(Hst_elts key l_log l)].
          rewrite(map_lub_elt_Some_None st_log st'_log key l_log E');
            first done.
          apply map_dom_None in F. rewrite Hst'_dom in F.
          destruct(st'_log !! key)eqn:G; last done.
          destruct F. by apply map_dom_Some in G.
        --rewrite lookup_insert_ne; last done.
          apply elem_of_union in Hxin as[?| ->%elem_of_singleton]; last (exfalso; by set_solver).
          by apply Hm_elts.
    - iIntros(v->). wp_match.
      destruct(st'_v_log !! key)eqn:E'; last first.
      { exfalso.
        apply map_dom_None in E; apply map_dom_None in E'.
        rewrite -Hst_dom -Hst'_dom in Hkey.
        set_solver. }
      wp_apply (wp_map_lookup (K := string) (V := val)); first done.
      rewrite E'.
      iIntros(st'_v->). wp_match.
      wp_apply (wp_map_insert (K := string) (V := val) _ key ); first done.
      iIntros(st''_v Hst'').
      iApply"Hφ".
      iPureIntro.
      split; last by rewrite map_lat_lub_dom.
      exists(<[key:=v]> m); repeat split; [| done |].
      * rewrite-Hm_dom.
        replace (gset_dom(<[key:=v]> m))with(dom(<[key:=v]> m)); last set_solver. 
        replace (gset_dom m) with (dom m); last set_solver. 
        set_solver.
      * intros x Hxin.
        destruct (st'_log !! key)eqn:F; first last.
        { apply map_dom_None in F. apply map_dom_Some in E'.
          by rewrite Hst'_dom in E'. }
        destruct(decide(x = key))as[->| J].
        --exists v, l; repeat split;
            [ by rewrite lookup_insert | | by apply(Hst'_elts key l v)].
          rewrite(map_lub_elt_None_Some st_log st'_log key l F);
            first done.
          apply map_dom_None in E. rewrite Hst_dom in E.
          destruct(st_log !! key)eqn:G; last done.
          destruct E. by apply map_dom_Some in G.
        --rewrite lookup_insert_ne; last done.
          apply elem_of_union in Hxin as[?| ->%elem_of_singleton]; last (exfalso; by set_solver).
          by apply Hm_elts.
  Qed.

  Lemma map_merge_st_spec merge_fn :
    @merge_spec LogOp LogSt _ _ _ _ _ _ _ PA merge_fn -∗
    @merge_spec _ _ _ _ _ _ _ _ _ map_params
    (λ: "st1" "st2", map_comb_merge merge_fn "st1" "st2").
  Proof.
    iIntros"#Hmerge"(addr st_v st'_v s s' st_log st'_log φ)
      "!>((%m&%Hst_coh&%Hst_dom&%Hst_elts)&(%m'&%Hst'_coh&%Hst'_dom&%Hst'_elts)&%Hs_den&%Hs'_den&
        %Hevents_ext&%Hsame_orig_comp&%Hevents_ext'&%Hsame_orig_comp') Hφ".
    do 2 (wp_lam; wp_pures).
    wp_apply wp_map_dom; first done; iIntros(dom_m_v Hdom_m_v); wp_let.
    wp_apply wp_map_dom; first done; iIntros(dom_m'_v Hdom_m'_v); wp_pures.
    wp_apply wp_set_union; first done; iIntros(dom_v Hdom_v); wp_pures.
    wp_apply wp_map_empty; first done; iIntros(empty_v Hempty_v).
    (** TODO: [wp_set_foldl] using the former lemma on the handler. *)
    iApply (wp_set_foldl);
    [ iIntros (key acc_v Xacc);
      iPoseProof ((bloup _ merge_fn
        st_v st'_v m m' st_log st'_log s s' Hs_den Hs'_den key acc_v Xacc
        Hevents_ext Hsame_orig_comp Hevents_ext' Hsame_orig_comp')
        with "[][]Hmerge")
        as "#Haux"; [done | done | iApply "Haux" ]
    | iPureIntro;
      repeat split; [ done |
        exists ∅; repeat split; try done;
        apply set_eq; set_solver
        | intros?; set_solver]|].
    iNext.
    iIntros(res_v ((res_log&Hdom&His_map&Helts)&Hset)).
    iApply "Hφ".
    iPureIntro.
    exists (map_lat_lub st_log st'_log); split; last reflexivity.
    exists res_log.
    repeat split;
      [ assumption
      | rewrite map_lat_lub_dom Hdom;
        by replace (dom m ∪ dom m') with (gset_dom st_log  ∪gset_dom st'_log);
          last set_solver|].
    intros k elt_v elt_log Hres_log Hlub.
    by destruct (Helts k)as(?&?&?&?&?);
      [ (rewrite-Hdom; by apply map_dom_Some in Hres_log)
      | simplify_eq/=].
  Qed.

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

  Lemma map_init_spec `{!StLib_Res mapOp} cA :
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
    iIntros "#HA #Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /map_comb_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply map_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & Hget & Hupdate)".
    wp_pures.
    iApply "HΦ"; iFrame.
  Qed.

End Bloup.


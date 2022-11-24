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

Lemma map_dom_None {E E'} `{!EqDecision E, !Countable E} (m: gmap E E') u:
  m !! u = None → u ∉ gset_dom m.
Proof. by intros?%not_elem_of_dom. Qed.
Lemma map_dom_Some {E E'} `{!EqDecision E, !Countable E} (m: gmap E E') u v:
  m !! u = Some v → u ∈ gset_dom m.
Proof. by intros?%elem_of_dom_2. Qed.

Section Bloup.

  Context `{latA: Lattice LogSt, !EqDecision LogOp, !Countable LogOp,
            !@CrdtDenot LogOp LogSt timestamp_time _ _, !CRDT_Params,
            inj_st: Inject LogSt val}.
  Context {p: StLib_Params LogOp LogSt}.

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

  Lemma map_lat_lub_dom (m m': mapSt):
    gset_dom (map_lat_lub m m') = (gset_dom m) ∪ (gset_dom m').
  Proof.
    generalize dependent m'. induction m' using map_ind.
    - rewrite/map_lat_lub map_fold_empty.
      replace (gset_dom ∅) with (∅: gset string);
        [ set_solver | by apply set_eq ].
    - rewrite/map_lat_lub.
      rewrite map_fold_insert; last assumption.
  Admitted.

  Lemma map_lub_elt_Some_Some (m m': gmap string LogSt) (s: string)
    (v v': LogSt):
    m !! s = Some v → m' !! s = Some v' →
    (map_lat_lub m m') !! s = Some (latA.(lat_lub) v v').
  Proof.
    generalize dependent m';
    generalize dependent s;
    generalize dependent v;
    generalize dependent v';
    generalize dependent m.
    induction m as [|s' v'' m Hm's' IH] using map_ind; first inversion 1.
    intros v' v s m' Hms Hm's.
  Admitted.

  Lemma map_lub_elt_Some_None (m m': gmap string LogSt) (s: string)
    (v: LogSt):
    m !! s = Some v → m' !! s = None →
    (map_lat_lub m m') !! s = Some v.
    Admitted.
  Lemma map_lub_elt_None_Some (m m': gmap string LogSt) (s: string)
    (v: LogSt):
    m' !! s = Some v → m !! s = None →
    (map_lat_lub m m') !! s = Some v.
    Admitted.
  Lemma map_lub_elt_None_None (m m': gmap string LogSt) (s: string):
    m !! s = None → m' !! s = None → (map_lat_lub m m') !! s = None.
    Admitted.

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
        rewrite (map_lub_elt_Some_Some m m' s v v' Hms Hm's).
        split; first trivial.
        by apply lat_lub_le_l.
      + exists v. by rewrite (map_lub_elt_Some_None m m' s v Hms Hm's).
    - intros s v' Hm's.
      destruct (m !! s) as [ v | ] eqn:Hms.
      + exists (latA.(lat_lub) v v').
        rewrite (map_lub_elt_Some_Some _ _ _ _ _ Hms Hm's).
        split; first trivial. by apply lat_lub_le_r.
      + exists v'. by rewrite (map_lub_elt_None_Some _ _ _ _ Hm's Hms).
    - intros m'' Hle Hle' s vlub Hlubs.
      destruct (m !! s) as [v|]eqn:Hms; destruct (m' !! s) as [v'|]eqn:Hm's.
      + pose proof (Hle s v Hms) as (v'' & Hv'' & Hle'').
        pose proof (Hle' s v' Hm's) as (v''_bis & Hv''_bis & Hle''_bis).
        assert(v''_bis = v'') as ->. { by simplify_eq. }
        exists v''. split; first trivial.
        rewrite (map_lub_elt_Some_Some _ _ _ _ _ Hms Hm's) in Hlubs.
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
    ∧ ∀ (str: string) (v: LogSt), st !! str = Some v →
      crdt_denot (
        gset_map
          (λ e, {|EV_Op := e.(EV_Op).2;
                  EV_Orig := e.(EV_Orig);
                  EV_Time := e.(EV_Time) |})
        (filter (λ ev, ev.(EV_Op).1 = str) s)) v.

  Global Instance map_denot_fun : Rel2__Fun map_denot_def.
  Proof.
    constructor. intros s m m' [Hdom Helts][Hdom' Helts'].
    apply map_eq. intros u.
    destruct (m !! u)as[v|]eqn:Hms; destruct (m' !! u)as[v'|]eqn:Hm's.
    - pose proof (Helts u v Hms) as A. pose proof (Helts' u v' Hm's) as B.
      destruct (H.(crdt_denot_fun))as [Hden].
      by rewrite Hms Hm's (Hden
        (gset_map
        (λ e : Event mapOp,
           {|
             EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e
           |}) (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = u) s))
        v v' A B).
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

  Lemma map_mut_lub_coh:
    ∀ (s1 s2 : event_set mapOp) (st1 st2 st3 : mapSt),
      ⟦ s1 ⟧ ⇝ st1
      → ⟦ s2 ⟧ ⇝ st2
        → Lst_Validity s1
          → Lst_Validity s2
            → Lst_Validity (s1 ∪ s2) → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    intros s1 s2 st1 st2?[Hdom1 Hden1][Hdom2 Hden2]Hv1 Hv2 Hv3<-.
    split; first by rewrite map_lat_lub_dom Hdom1 Hdom2 gset_map_union.
    intros s v Hs.
    destruct (st1 !! s) as [l |] eqn:E;
    destruct (st2 !! s) as [l' |] eqn:E';
    last (exfalso; pose proof (map_lub_elt_None_None st1 st2 s E E');
      by rewrite H1 in Hs).
    - pose proof (map_lub_elt_Some_Some st1 st2 s l l' E E').
      replace (gset_map
        (λ e : Event (string * LogOp),
           {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
        (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) (s1 ∪ s2)))
        with (
          (gset_map
                (λ e : Event (string * LogOp),
                   {|
                     EV_Op := (EV_Op e).2;
                     EV_Orig := EV_Orig e;
                     EV_Time := EV_Time e
                   |})
                (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s)
                   s1))
          ∪ (gset_map
                (λ e : Event (string * LogOp),
                   {|
                     EV_Op := (EV_Op e).2;
                     EV_Orig := EV_Orig e;
                     EV_Time := EV_Time e
                   |})
                (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s)
                   s2))); last set_solver.
      specialize Hden1 with s l.
      (*pose proof (p.(StLib_Model).(st_crdtM_lub_coh)
        (gset_map
          (λ e : Event (string * LogOp),
             {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
          (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) s1))
        (gset_map
          (λ e : Event (string * LogOp),
             {| EV_Op := (EV_Op e).2; EV_Orig := EV_Orig e; EV_Time := EV_Time e |})
          (filter (λ ev : Event (string * LogOp), (EV_Op ev).1 = s) s2))
        l l' (l ⊔_l l') (Hden1 E)).*) admit.
    - admit.
    - admit.
  Admitted.

  Lemma map_mut_coh:
    ∀ (s : event_set mapOp) (st st' : mapSt) (ev : Event mapOp),
      ⟦ s ⟧ ⇝ st
      → Lst_Validity s
        → ev ∉ s
          → is_maximum ev (s ∪ {[ev]})
            → map_mutator st ev st' → ⟦ s ∪ {[ev]} ⟧ ⇝ st'. Admitted.

  Lemma map_mut_mon (m : mapSt) (e : Event mapOp) (m' : mapSt) :
    map_mutator m e m' → m ≤_l m'.
  Proof.
    intros(Hdom&Hold_v&Hnew_v&Hnew_v')s v Hmsv.
    destruct(decide(s = (EV_Op e).1)) as[-> | ].
    + destruct (Hnew_v _ Hmsv)as(v'&Hmut&Hm'sv').
      exists v'. split; first assumption.
      by apply st_crdtM_mut_mon with (map_event e).
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
        string_serialization p.(StLib_StSerialization)).

  Definition map_op_coh (op: mapOp) (v: val): Prop :=
    ∃(s: string)(lop: LogOp)(vs vop: val),
      op.1 = s ∧ op.2 = lop
      ∧ v = (vs, vop)%V
      ∧ p.(StLib_Op_Coh) lop vop
      ∧ vs = #s.

  Definition map_st_coh (st: mapSt) (v: val): Prop := is_map v st.

  Lemma map_coh_ser:
    ∀ (st : mapSt) (v : val), map_st_coh st v → Serializable map_ser v.
    Admitted.

  Global Instance map_params : StLib_Params mapOp mapSt.
  Proof.
    refine {|
      StLib_StSerialization := map_ser;
      StLib_Op_Coh := map_op_coh;
      StLib_St_Coh := map_st_coh;
      StLib_Denot := map_denot;
      StLib_Model := map_model; |}.
    - intros [ol or][ol' or'] v
        (s & lop & vs & vop & Hseq & Hlopeq & Hveq & Hlopcoh & Hvsq)
        (s'& lop'& vs'& vop'& Hseq'& Hlopeq'& Hveq'& Hlopcoh'& Hvsq').
      f_equal; first by simplify_eq/=.
      simplify_eq/=. by apply (p.(StLib_Op_Coh_Inj)lop lop' vop').
    - intros st st' v (l&->&Hl&H'l)(l'&->&Hl'&H'l').
      assert(l=l') as ->; last reflexivity.
      rewrite Hl in Hl'. by apply inject_inj.
    - exact map_coh_ser.
  Defined.

End Bloup.

Section MapComp_Proof.
  Context (LogOp : Type) (LogSt : Type).
  Context `{!EqDecision LogOp} `{!Countable LogOp}.
  Context `{!Inject LogSt val}.
  Context `{lat : Lattice LogSt}.
  Context `{a: anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{PA : !StLib_Params LogOp LogSt}.

  Lemma map_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ (@mapOp LogOp) _ _ (@mapSt LogSt) _ _ _
      map_comb_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /map_comb_init_st.
    wp_pures. wp_apply wp_map_empty; first trivial.
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro.
    by rewrite/StLib_St_Coh/map_params/map_st_coh/st_crdtM_init_st/StLib_Model/map_model.
  Qed.

  Lemma map_mutator_st_spec mut_fn init_fn :
    @init_st_fn_spec _ _ _ LogOp _ _ LogSt _ _ PA init_fn -∗
    (** TODO: Init !!! *)
    @mutator_spec _ _ _ _ _ _ LogSt _ _ PA mut_fn -∗
    @mutator_spec _ _ _ _ _ _ _ _ _ map_params
      (λ: "i" "gs" "op", map_comb_mutator init_fn mut_fn "i" "gs" "op").
  Proof.
    iIntros "#Hinit #Hmut" (addr id st_v op_v s ev op_log st_log)
                 "!> %φ ((%s'&%lop&%vs&%vop&%Hop1&%Hop2&->&%Hop_coh&->) & (%l_st&->&%Hst_v&%Hst_v') & %Hden & %Hnin & %Hop & %Horig &
                 %Hmax & %Hevent_ext & %Hcomp) Hφ".
    do 5 wp_pure _. wp_lam. do 14 wp_pure _.
    wp_bind (map_lookup _ _)%E.
    replace (#s') with ($ s'); last done. rewrite Hst_v.
    iApply (wp_map_lookup with "[]"); first (iPureIntro; by exists l_st).
    iNext. iIntros (v_st_s').
    destruct (list_to_map l_st !! s') eqn:E.
    - iIntros (->).
      wp_match.
      wp_apply ("Hmut" with "[]").
      { iPureIntro. admit. }
      iIntros (st' (log_st'&Hst'_coh & Hmut)).
      wp_let.
      admit.
    - iIntros (->). do 3 wp_pure _.
      wp_apply "Hinit"; first trivial. iIntros (vinit Hinit).
      wp_apply ("Hmut" with "[]").
      { iPureIntro. admit. }
      iIntros (st' (log_st'&Hst'_coh & Hmut)).
      do 2 wp_pure _.
  Admitted.

  Lemma map_merge_st_spec merge_fn :
    @merge_spec _ _ _ _ _ _ LogSt _ _ PA merge_fn -∗
    @merge_spec _ _ _ _ _ _ _ _ _ map_params
    (λ: "st1" "st2", map_comb_merge merge_fn "st1" "st2").
  Proof.
    iIntros "#Hmerge" (??????? φ)
      "!>(%Hst_coh&%Hst_coh'&%Hden&%Hden'&%Hext&%Hcomp&%Hext'&%Hcomp') Hφ".
    wp_lam. wp_let. wp_lam. wp_pures.
    wp_apply wp_map_dom; first (iPureIntro; apply Hst_coh).
    iIntros (v_st_dom Hv_st_dom). wp_let.
    wp_apply wp_map_dom; first (iPureIntro; apply Hst_coh').
    iIntros (v_st'_dom Hv_st'_dom). wp_let.
    wp_apply (wp_set_union); first done.
    iIntros (v_dom Hv_dom). wp_let.
    do 3 wp_pure _.
    wp_bind (map_code.map_empty _)%E.
    wp_apply wp_map_empty; first trivial. iIntros (st_empty His_empty).
    wp_smart_apply wp_set_foldl.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma map_crdt_fun_spec cA :
    @crdt_fun_spec _ _ _ _ _ _ LogSt _ _ PA cA -∗
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
    @crdt_fun_spec _ _ _ _ _ _ LogSt _ _ PA cA -∗
    @init_spec
      _ _ _ _ _ _ _ _ _ map_params _
      (statelib_init
        (string_map_ser
            (PA.(StLib_StSerialization).(s_serializer)).(s_ser))
        (string_map_deser
            (PA.(StLib_StSerialization).(s_serializer)).(s_deser))) -∗
    @init_spec_for_specific_crdt _ _ _ _ _ _ _ _ _  map_params _
      (λ: "addrs" "rid",
         map_comb_init
          (PA.(StLib_StSerialization).(s_serializer)).(s_ser)
          (PA.(StLib_StSerialization).(s_serializer)).(s_deser)
          cA "addrs" "rid").
  Proof.
  Admitted.

End MapComp_Proof.


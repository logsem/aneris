From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
Import derived_laws_later.bi.


(* TODO: is it already done somewhere? *)
Section GsetMap.
  Context {M N} `{EqDecision M} `{EqDecision N} `{Countable M} `{Countable N}. 

  Definition gset_map (f: M -> N) (m: gset M): gset N :=
    list_to_set (f <$> elements m).

  Lemma gset_map_spec (f: M -> N) (m: gset M):
    forall b, b ∈ gset_map f m <-> exists a, a ∈ m /\ f a = b.
  Proof using.
    intros. unfold gset_map. split; intros. 
    - apply elem_of_list_to_set in H1.
      apply elem_of_list_fmap_2 in H1 as [a [-> IN]].
      eexists. split; eauto. eapply elem_of_elements; eauto.
    - destruct H1 as [a [IN <-]].
      apply elem_of_list_to_set. apply elem_of_list_fmap_1.
      eapply elem_of_elements; eauto.
  Qed. 

  (* TODO: only holds for injective functions *)
  (* Lemma gset_map_spec' (f: M -> N) (m: gset M): *)
  (*   forall a, f a ∈ gset_map f m <-> a ∈ m.  *)

  Lemma gset_map_in (f: M -> N) m a (IN: a ∈ m):
    f a ∈ gset_map f m.
  Proof using.
    unfold gset_map. apply elem_of_list_to_set.
    apply elem_of_list_fmap_1. apply elem_of_elements; auto.
  Qed. 

End GsetMap.

(* TODO: ? generalize to Model *)
Section ExtModels2.
  Context (M: FairModel).
  (* TODO: ??? *)
  (* Context (ETs: list (relation (fmstate M))). *)
  (* Context {EI: Type} (ETs: EI -> (fmstate M -> fmstate M -> Prop)). *)
  (* ext transitions index *)
  Context {EI: Type} {DecEI: EqDecision EI} {CntEI: Countable EI}.
  Context (ETs: EI -> option (fmstate M -> fmstate M -> Prop)).
  Hypothesis next_ext_dec:
    forall i rel st (EXTi: ETs i = Some rel),
      Decision (∃ st', rel st st'). 


  (* Definition add_indices := {i: nat | i < length ETs}.  *)
  (* TODO: rename? *)
  (* Inductive env_role := env (i: nat).  *)
  Inductive env_role := env (i: EI).
  Definition ext_role: Type := (fmrole M + env_role). 

  Global Instance env_role_EqDec: EqDecision env_role. 
  Proof using DecEI. solve_decision. Qed. 

  Global Instance env_role_cnt: Countable env_role. 
  Proof using CntEI.
    destruct CntEI.
    refine {| 
        encode r := match r with | env i => encode i end;
        decode i := match (decode i) with | Some r => Some (env r) | None => None end
      |}.
    intros. destruct x.
    by rewrite decode_encode.
  Qed.

  Inductive ext_trans: fmstate M -> option ext_role -> fmstate M -> Prop :=
  | ext_model_step s1 ρ s2 (STEP: fmtrans M s1 (Some ρ) s2):
    ext_trans s1 (Some (inl ρ)) s2
  | ext_ext_step s1 s2 i rel (EXTi: ETs i = Some rel) (REL: (rel s1 s2: Prop)):
    ext_trans s1 (Some (inr (env i))) s2. 

  (* (* TODO: rename? *) *)
  (* Definition env_role': gset env_role := *)
  (*   list_to_set (map env (seq 0 (length ETs))). *)
  
  Instance next_ext_dec':
    ∀ st x, Decision ((λ ρ, ∃ st', ext_trans st (Some (inr ρ)) st') x).
  Proof using next_ext_dec. 
    intros st [i].
    destruct (ETs i) eqn:RELi.
    2: { right. intros [st' STEP]. inversion STEP. congruence. }
    specialize (@next_ext_dec i P st RELi).
    destruct next_ext_dec as [EX | NEX]; auto. 
    - left. destruct EX as [st' TRANS].
      exists st'. econstructor; eauto.
    - right. intros [st' TRANS]. destruct NEX.
      inversion TRANS. subst. 
      exists st'. congruence. 
  Qed.

  (* TODO: is it possible to express the inr lifting 
     without requiring the decidability above? *)
  Definition ext_live_roles (st: fmstate M): gset ext_role :=
    gset_map inl (live_roles M st) ∪
    gset_map inr (filter (fun ρ => exists st', ext_trans st (Some (inr ρ)) st') env_role').

  Lemma ext_live_spec:
    ∀ s ρ s', ext_trans s (Some ρ) s' → ρ ∈ ext_live_roles s.
  Proof using.
    intros s ρ s' TRANS. unfold ext_live_roles.
    inversion TRANS; subst; simpl in *.
    - apply elem_of_union_l. apply gset_map_in.
      eapply fm_live_spec; eauto. 
    - apply elem_of_union_r. apply gset_map_in.
      apply elem_of_filter.
      split.
      { exists s'. eauto. }
      unfold env_role'. apply elem_of_list_to_set.
      apply elem_of_list_fmap_1. apply elem_of_seq.
      apply lookup_lt_Some in EXTi. lia.
  Qed.
                      
  Definition ext_model: FairModel.
  Proof using next_ext_dec M ETs.
    refine({|
              fmstate := fmstate M;
              fmrole := ext_role;
              fmtrans := ext_trans;
              live_roles := ext_live_roles;
              fm_live_spec := ext_live_spec
            |}).
    apply M. 
  Defined.

End ExtModels2. 


Section SetFairness.
 
  Definition set_fair_model_trace {M} (T: gset (fmrole M)) tr :=
    forall ρ (Tρ: ρ ∈ T), fair_model_trace ρ tr. 

End SetFairness.

Section Model.

  Let tl_role := nat. 

  (* TODO: how to make Inductive and Record section-local? *)
  Inductive tl_role_stage := 
  | tl_L
  | tl_U (t: nat)
  .

  Let tl_role_st: Set := tl_role_stage * bool. 

  Let tl_role_map := gmap tl_role tl_role_st. 

  Record tl_st := mkTlSt {
      owner: nat;
      ticket: nat;
      role_map: tl_role_map
    }. 

  #[global] Instance tl_role_stage_eqdec: EqDecision tl_role_stage. 
  Proof using. solve_decision. Qed. 
  
  #[global] Instance tl_role_st_eqdec: EqDecision tl_role_st. 
  Proof using. solve_decision. Qed. 

  #[global] Instance tl_st_eqdec: EqDecision tl_st. 
  Proof using. solve_decision. Qed. 
  
  (* #[global] Instance YN_countable: Countable YN. *)
  (* Proof. *)
  (*   refine ({| *)
  (*              encode yn := match yn with Y => 1 | No => 2 end; *)
  (*              decode p := match p with 1 => Some Y | 2 => Some No | _ => None end; *)
  (*            |})%positive. *)
  (*   intros yn. by destruct yn. *)
  (* Qed. *)

  (* #[global] Instance YN_inhabited: Inhabited YN. *)
  (* Proof. exact (populate Y). Qed. *)

  (* Global Instance lookup_tl_role_map: *)
  (*   Lookup tl_role (tl_role_stage * bool) tl_role_map.  *)
  (* Proof using.  *)
  (*   red. intros r rm. *)
  (*   set (o := rm !! r).  *)

  (* Lemma foo (rm: tl_role_map) (r: tl_role): *)
  (*   rm !! r = Some (tl_L, true).  *)
  
  Lemma role_of_dec (rm: tl_role_map) (s: tl_role_st):
    {r | rm !! r = Some s} + (forall r, rm !! r ≠ Some s). 
  Proof using.
    pose proof (map_eq_dec_empty (filter (fun '(_, s') => s = s') rm)).
    destruct H as [NIN | IN].
    { right. intros r IN. 
      eapply map_filter_empty_not_lookup in NIN; eauto. }
    left. apply choice; eauto.
    { intros. solve_decision. }
    apply map_choose in IN. destruct IN as (r & s' & IN).
    apply map_filter_lookup_Some in IN. destruct IN as [IN <-]. eauto.
  Qed.  

  Let advance_next (st: tl_st) := 
        match role_of_dec (role_map st) (tl_U (owner st), true) with
        | inl (exist _ r _) => 
            let rm' := <[r := (tl_U (owner st), false)]> (role_map st) in
            mkTlSt (owner st) (ticket st) rm'
        | inr NO => st
        end.

  Inductive tl_trans: tl_st -> option tl_role -> tl_st -> Prop :=
  | tl_acquire_lock o rm r (R: rm !! r = Some (tl_L, true)):
    tl_trans (mkTlSt o o rm) (Some r) (mkTlSt o (o + 1) (<[r := (tl_U o, false)]> rm))
  | tl_acquire_wait o t rm r (LT: o < t) (R: rm !! r = Some (tl_L, true)):
    tl_trans (mkTlSt o t rm) (Some r) (mkTlSt o (t + 1) (<[r := (tl_U t, true)]> rm))    
  | tl_spin o t k rm r (LT: o < k) (R: rm !! r = Some (tl_U k, true)):
    tl_trans (mkTlSt o t rm) (Some r) (mkTlSt o t rm)
  | tl_unlock o t rm r (R: rm !! r = Some (tl_U o, true)):
    let st' := (mkTlSt (o + 1) t (<[r := (tl_L, false)]> rm)) in
    let st'' := advance_next st' in
    tl_trans (mkTlSt o t rm) (Some r) st''
  .

  Definition tl_live_roles (st: tl_st): gset tl_role :=
    dom (filter (fun '(r, (_, e)) => e = true) (role_map st)).

  Lemma live_spec_holds:
    forall s ρ s', tl_trans s (Some ρ) s' -> ρ ∈ tl_live_roles s.
  Proof.
    intros s ρ s' TRANS. rewrite /tl_live_roles.
    inversion TRANS; subst; simpl. 
    all: eapply elem_of_dom_2; apply map_filter_lookup_Some_2; done.
  Qed.

  #[global] Instance tlSt_inhabited: Inhabited tl_st. 
  Proof. exact (populate (mkTlSt 0 0 ∅)). Qed.

  Definition tl_fair_model: FairModel.
  Proof.
    refine({|
              fmstate := tl_st;
              fmrole := tl_role;
              fmtrans := tl_trans;
              live_roles := tl_live_roles;
              fm_live_spec := live_spec_holds;
            |}).
  Defined.

  Inductive allows_unlock : tl_st -> tl_st -> Prop :=
  | adds_unlock_step o t ρ rm (LOCK: rm !! ρ = Some (tl_U o, false)):
    allows_unlock (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_U o, true)]> rm))
  .

  Definition tl_ext_trans := [allows_unlock]. 

  Lemma tl_next_ext_dec: 
    ∀ i rel st, tl_ext_trans !! i = Some rel → Decision (∃ st', rel st st').
  Proof using. 
    unfold tl_ext_trans. intros ? ? ? RELi.
    destruct i; try done. simpl in *. inversion RELi. subst. clear RELi.
    destruct st as [o t rm]. 
    destruct (role_of_dec rm (tl_U o, false)) as [[r LOCK] | FREE].
    - left. eexists. econstructor. eauto.
    - right. intros [st' TRANS]. inversion TRANS. subst.
      edestruct FREE; eauto.
  Qed. 
  
  Section ProgressProperties.
    Context {tr: mtrace (ext_model tl_fair_model [allows_unlock] tl_next_ext_dec)}. 

  End ProgressProperties. 

End Model. 

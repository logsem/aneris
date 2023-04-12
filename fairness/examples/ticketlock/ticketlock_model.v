From iris.proofmode Require Import tactics.
From hahn Require Import HahnBase.
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
From trillium.fairness.examples.ticketlock Require Import lemmas. 
From trillium.fairness.examples.ticketlock Require Import trace_len.


(* TODO: inherited from hahn? *)
Close Scope Z_scope. 


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

  Lemma gset_map_in_inj (f: M -> N) m a (INJ: injective f):
    a ∈ m <-> f a ∈ gset_map f m.
  Proof using.
    split; [apply gset_map_in| ]. intros IN.
    apply gset_map_spec in IN as [b [IN EQ]].
    apply INJ in EQ. congruence.
  Qed. 

End GsetMap.


Section GsetMapProperties.

  Lemma gset_map_compose {M N T} 
    `{EqDecision M} `{EqDecision N} `{EqDecision T}
    `{Countable M} `{Countable N} `{Countable T}
    (f: M -> N) (g: T -> M) m:
    gset_map (f ∘ g) m = gset_map f (gset_map g m). 
  Proof using.
    set_solver.
  Qed. 
  
End GsetMapProperties.


Section TraceHelpers0.

  Lemma pred_at_dec {St L: Type} (P: St → option L → Prop)
    (DEC: forall st ro, Decision (P st ro)):
    forall i tr, Decision (pred_at tr i P).
  Proof using.
    intros i tr. unfold pred_at.
    destruct (after i tr); [destruct t| ]; auto.
    solve_decision.
  Qed.

  (* Lemma trace_lookup_dec {St L: Type} (P: St → option L → Prop) *)
  (*   (DEC: forall st ro, Decision (P st ro)): *)
  (*   forall i tr, Decision (pred_at tr i P). *)
  (* Proof using. *)
  (*   intros i tr. unfold pred_at. *)
  (*   destruct (after i tr); [destruct t| ]; auto. *)
  (*   solve_decision. *)
  (* Qed. *)

End TraceHelpers0. 

Section TraceDefinitions.
  Context {M: FairModel}.
  
  (* Definition mtrace_nth_pred_at (t: mtrace M) (i: nat) (st: fmstate M) P *)
  (*                               (ITH: mtrace_nth t i = Some st): *)
  (*   pred_at t i P <-> forall ol, P st ol.  *)
  (* Admitted.  *)

  
  
  (* Definition fair_model_trace_strong ρ (mtr: mtrace M): Prop  := *)
  (*   forall n, pred_at mtr n (λ δ _, role_enabled_model ρ δ) -> *)
  (*        ∃ m, ClassicalFacts.Minimalpred_at mtr (n+m) (λ δ _, ¬role_enabled_model ρ δ) *)
  (*             ∨ pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)). *)

  (* TODO: already exists somewhere? *)
  Lemma Decision_iff_impl (P Q: Prop) (PQ: P <-> Q) (DEC_P: Decision P):
    Decision Q. 
  Proof using. 
    destruct DEC_P; [left | right]; tauto. 
  Qed.

  Lemma pred_at_or P1 P2 (tr: mtrace M) i: 
    pred_at tr i P1 \/ pred_at tr i P2 <-> pred_at tr i (fun x y => P1 x y \/ P2 x y).
  Proof using.
    unfold pred_at. destruct (after i tr); [destruct t| ]; tauto.
  Qed.

  (* Lemma pred_at_neg P: *)
  (*   forall (tr: mtrace M) i, pred_at tr i (fun x y => ¬ P x y) <-> ¬ pred_at tr i P. *)
  (* Proof using. *)
  (*   intros. unfold pred_at. *)
  (*   destruct (after i tr); [destruct t| ]; try tauto. *)
  (* Qed. *)

  (* TODO: rewrite as Instance *)
  (* Instance pred_at_mono {St L : Type}: *)
  (*   (* Proper (eq ==> eq ==> pointwise_relation St L eq ==> eq ==> iff) (@pred_at St L).  *) *)
  (* Proof using. *)

  (* Lemma pred_at_mono {St L : Type} (P Q: St -> option L -> Prop) *)
  (*   (PQ: forall s l, P s l -> Q s l): *)
  (*   forall tr i, pred_at tr i P -> pred_at tr i Q. *)
  (* Proof using. *)
  (*   rewrite /pred_at. intros. destruct (after i tr); [destruct t| ]; auto. *)
  (* Qed.        *)
  

  Definition strong_fair_model_trace (tr: mtrace M) (ρ: fmrole M) :=
    forall n (EN: pred_at tr n (λ δ _, role_enabled_model ρ δ)),
    exists m, ClassicalFacts.Minimal 
                (fun x => pred_at tr (n+x) (λ δ ℓ, ¬ role_enabled_model ρ δ \/ 
                                                     ℓ = Some (Some ρ))) m.


  Lemma fair_model_trace_defs_equiv (tr: mtrace M) (ρ: fmrole M):
    fair_model_trace ρ tr <-> strong_fair_model_trace tr ρ.
  Proof using. 
    split.
    2: { intros FAIR. red. intros.
         red in FAIR. specialize (FAIR n H) as [m [FAIR MIN]].
         exists m. by apply pred_at_or. }

    intros FAIR. red. intros.
    red in FAIR.
    specialize (@FAIR n). destruct FAIR; auto.

    pattern x in H. eapply min_prop_dec in H as [d MIN].
    { clear x. exists d. 
      eapply Minimal_proper; eauto. 
      red. intros. symmetry. apply pred_at_or. }

    intros. eapply Decision_iff_impl. 
    { symmetry. apply pred_at_or. }
    apply pred_at_dec. intros.
    apply or_dec.
    2: { solve_decision. }
    apply not_dec.
    rewrite /role_enabled_model. solve_decision.
  Qed. 
  
  Definition strong_fair_model_trace_alt (tr: mtrace M) (ρ: fmrole M) :=
    forall n st (NTH: tr S!! n = Some st) (EN: role_enabled_model ρ st),
    exists m, ClassicalFacts.Minimal (
             fun x => (exists st', tr S!! (n + x) = Some st' /\ 
                             ¬ role_enabled_model ρ st') \/
                     (tr L!! (n + x) = Some (Some ρ))
           ) m. 

  Lemma strong_fair_model_trace_alt_defs_equiv (tr: mtrace M) (ρ: fmrole M):
    strong_fair_model_trace tr ρ <-> strong_fair_model_trace_alt tr ρ.
  Proof using. 
    rewrite /strong_fair_model_trace /strong_fair_model_trace_alt. 
    pose proof trace_has_len tr as [len LEN]. 
    split; intros. 
    - specialize (H n). specialize_full H. 
      { apply pred_at_trace_lookup. eauto. }
      destruct H as [m [PROP MIN]]. exists m. split.
      { apply pred_at_or in PROP as [PROP | PROP];
          [left | right]; apply pred_at_trace_lookup in PROP; desc; eauto. }
      intros. apply MIN. apply pred_at_trace_lookup.
      destruct H as [DIS | STEP].
      { desc. exists st'. eauto. }
      forward eapply (proj1 (label_lookup_states tr (n + k))) as [[st' ST'] _]; eauto.
    - apply pred_at_trace_lookup in EN. desc. 
      specialize (H _ _ EN EN0). desc. destruct H as [PROP MIN].  
      exists m. split.
      + apply pred_at_trace_lookup. destruct PROP as [DIS | STEP]; desc; eauto.
        forward eapply (proj1 (label_lookup_states tr (n + m))) as [[st' ST'] _]; eauto.
      + intros. apply MIN. apply pred_at_or in H. destruct H as [DIS | STEP].
        * left. apply pred_at_trace_lookup in DIS. eauto. 
        * right. apply pred_at_trace_lookup in STEP. desc. eauto. 
  Qed.        
  

End TraceDefinitions.   



(* TODO: ? generalize to Model *)
Section ExtModels2.
  Context (M: FairModel).
  (* TODO: ??? *)
  (* Context (ETs: list (relation (fmstate M))). *)
  (* Context {EI: Type} (ETs: EI -> (fmstate M -> fmstate M -> Prop)). *)
  (* ext transitions index *)
  Context {EI: Type} {DecEI: EqDecision EI} {CntEI: Countable EI}.
  (* Context (ETs: EI -> option (fmstate M -> fmstate M -> Prop)). *)
  Context (ETs: EI -> relation (fmstate M)). 
  (* Hypothesis next_ext_dec: *)
  (*   forall i rel st (EXTi: ETs i = Some rel), *)
  (*     Decision (∃ st', rel st st').  *)
  Context (active_exts: fmstate M -> gset EI).
  Hypothesis (active_exts_spec: forall st ι, ι ∈ active_exts st <-> ∃ st', ETs ι st st').


  (* Definition add_indices := {i: nat | i < length ETs}.  *)
  (* TODO: rename? *)
  (* Inductive env_role := env (i: nat).  *)
  Inductive env_role := env (i: EI).
  Definition ext_role: Type := (fmrole M + env_role). 

  Global Instance env_role_EqDec: EqDecision env_role. 
  Proof using -DecEI. clear -DecEI. solve_decision. Qed. 

  Global Instance env_role_cnt: Countable env_role. 
  Proof.
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
  | ext_ext_step s1 s2 ι (REL: ETs ι s1 s2):
    ext_trans s1 (Some (inr (env ι))) s2. 

  (* (* TODO: rename? *) *)
  (* Definition env_role': gset env_role := *)
  (*   list_to_set (map env (seq 0 (length ETs))). *)
  
  (* Instance next_ext_dec': *)
  (*   ∀ st x, Decision ((λ ρ, ∃ st', ext_trans st (Some (inr ρ)) st') x). *)
  (* Proof using next_ext_dec.  *)
  (*   intros st [i]. *)
  (*   destruct (ETs i) eqn:RELi. *)
  (*   2: { right. intros [st' STEP]. inversion STEP. congruence. } *)
  (*   specialize (@next_ext_dec i P st RELi). *)
  (*   destruct next_ext_dec as [EX | NEX]; auto.  *)
  (*   - left. destruct EX as [st' TRANS]. *)
  (*     exists st'. econstructor; eauto. *)
  (*   - right. intros [st' TRANS]. destruct NEX. *)
  (*     inversion TRANS. subst.  *)
  (*     exists st'. congruence.  *)
  (* Qed. *)

  (* TODO: is it possible to express the inr lifting 
     without requiring the decidability above? *)
  Definition ext_live_roles (st: fmstate M): gset ext_role :=
    gset_map inl (live_roles M st) ∪
      (* gset_map inr (filter (fun ρ => exists st', ext_trans st (Some (inr ρ)) st') env_role'). *)
      gset_map (inr ∘ env) (active_exts st). 

  Lemma ext_live_spec:
    ∀ s ρ s', ext_trans s (Some ρ) s' → ρ ∈ ext_live_roles s.
  Proof using.
    intros s ρ s' TRANS. unfold ext_live_roles.
    inversion TRANS; subst; simpl in *.
    - apply elem_of_union_l. apply gset_map_in.
      eapply fm_live_spec; eauto. 
    - apply elem_of_union_r.
      rewrite gset_map_compose. do 2 apply gset_map_in.
      apply active_exts_spec. eauto.
  Qed.
  
  Definition ext_model: FairModel.
  Proof using All. 
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
  
  Definition set_fair_model_trace {M} (T: fmrole M -> Prop) tr :=
    forall ρ (Tρ: T ρ), fair_model_trace ρ tr. 

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

  Notation "<{ o , t , rm }>" := (mkTlSt o t rm).

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
  (* | tl_acquire_lock o rm r (R: rm !! r = Some (tl_L, true)): *)
  (*   tl_trans <{o, o, rm}> (Some r) <{o, o + 1, <[r := (tl_U o, false)]> rm }> *)
  (* | tl_acquire_wait (o t: nat) rm r (LT: o < t) (R: rm !! r = Some (tl_L, true)): *)
  (*   tl_trans <{o, t, rm}> (Some r) <{o, t + 1, <[r := (tl_U t, true)]> rm}> *)
  | tl_take_ticket o t rm r (R: rm !! r = Some (tl_L, true)):
    let next_en := if decide (o = t) then false else true in
    tl_trans <{o, t, rm}> (Some r) <{o, t + 1, <[r := (tl_U t, next_en)]> rm}>
  | tl_spin (o t k: nat) rm r (LT: o < k) (R: rm !! r = Some (tl_U k, true)):
    tl_trans <{o, t, rm}> (Some r) <{o, t, rm}>
  | tl_unlock o t rm r (R: rm !! r = Some (tl_U o, true)):
    let st' := <{o + 1, t, <[r := (tl_L, false)]> rm}> in
    let st'' := advance_next st' in
    tl_trans <{o, t, rm}> (Some r) st''
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

  
  Definition can_lock_st (ρ: tl_role) (st: tl_st) :=
    exists e, (role_map st) !! ρ = Some (tl_L, e). 

  Definition has_lock_st (ρ: tl_role) (st: tl_st) :=
    exists e, (role_map st) !! ρ = Some (tl_U (owner st), e). 

  Definition active_st (ρ: tl_role) (st: tl_st) :=
    exists r, (role_map st) !! ρ = Some (r, true).

  Lemma active_st_enabled (ρ: tl_role) (st: tl_st):
    active_st ρ st <-> @role_enabled_model tl_fair_model ρ st.
  Proof using. 
  Admitted. 

  Definition tl_init_st (n: nat): tl_st :=
    let rm := gset_to_gmap (tl_L, true) (set_seq 0 n) in
    <{ 0, 0, rm }>.


  Section TlExtTrans.

    Inductive allows_unlock : tl_st -> tl_st -> Prop :=
    | allows_unlock_step o t ρ rm (LOCK: rm !! ρ = Some (tl_U o, false)):
      allows_unlock (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_U o, true)]> rm))
    .

    Inductive allows_lock ρ : tl_st -> tl_st -> Prop :=
    | allows_lock_step t o rm (LOCK: rm !! ρ = Some (tl_L, false)):
      allows_lock ρ (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_L, true)]> rm))
    .

    Inductive tl_EI := eiU | eiL (ρ: tl_role).

    Definition tl_ETs (ι: tl_EI) := 
      match ι with
      | eiU => allows_unlock
      | eiL ρ => allows_lock ρ
      end. 

    Global Instance tl_EI_dec: EqDecision tl_EI. 
    Proof using. solve_decision. Qed. 

    Global Instance tl_EI_cnt: Countable tl_EI. 
    Proof using.
    Admitted.

    (* Lemma tl_next_ext_dec:  *)
    (*   ∀ i rel st, tl_ETs i = Some rel → Decision (∃ st', rel st st'). *)
    (* Proof using.  *)
    (*   unfold tl_ext_trans. intros ? ? ? RELi. *)
    (*   destruct i; try done. simpl in *. inversion RELi. subst. clear RELi. *)
    (*   destruct st as [o t rm].  *)
    (*   destruct (role_of_dec rm (tl_U o, false)) as [[r LOCK] | FREE]. *)
    (*   - left. eexists. econstructor. eauto. *)
    (*   - right. intros [st' TRANS]. inversion TRANS. subst. *)
    (*     edestruct FREE; eauto. *)
    (* Qed.  *)

    Lemma allows_unlock_ex_dec: 
      forall st, Decision (∃ st', allows_unlock st st'). 
    Proof using. 
      intros [o t rm]. 
      destruct (role_of_dec rm (tl_U o, false)) as [[r LOCK] | FREE].
      - left. eexists. econstructor. eauto.
      - right. intros [st' TRANS]. inversion TRANS. subst.
        edestruct FREE; eauto.
    Qed. 

    Instance allows_lock_ex_dec:
      forall st ρ, Decision (∃ st', allows_lock ρ st st'). 
    Proof using.
      intros [o t rm] ρ.
      destruct (decide (rm !! ρ = Some (tl_L, false))).
      - left. eexists. econstructor; eauto.
      - right. intros [st' L]. inversion L. congruence. 
    Qed. 

    Definition tl_active_exts st: gset tl_EI := 
      (if (allows_unlock_ex_dec st) then {[ eiU ]} else ∅) ∪
        gset_map eiL (filter (fun ρ => exists st', allows_lock ρ st st') 
                        (dom (role_map st))). 
    

    Lemma tl_active_exts_spec st ι:
      ι ∈ tl_active_exts st <-> ∃ st', tl_ETs ι st st'.
    Proof using. 
      unfold tl_active_exts.
      etransitivity; [apply elem_of_union| ].
      destruct ι; simpl in *.
      - etransitivity; [| etransitivity]; [| eapply or_False |].
        { eapply Morphisms_Prop.or_iff_morphism; set_solver. }
        destruct (allows_unlock_ex_dec st).
        2: { split; [set_solver| ]. intros [st' UNL]. 
             destruct n. exists st'. congruence. }
        destruct e as [st' UNL]. etransitivity; [apply elem_of_singleton| ].
        split; auto. intros _. eauto.
      - etransitivity; [| etransitivity]; [| eapply False_or |].
        { eapply Morphisms_Prop.or_iff_morphism; destruct (allows_unlock_ex_dec st); set_solver. }
        etransitivity.
        { symmetry. apply @gset_map_in_inj with (f := eiL).
          red. intros. congruence. }
        etransitivity; [apply elem_of_filter| ].
        simpl.  
        split; [intros [[? ?] ?] | intros [? [FF]]]; eauto. 
        simpl. split.
        + eexists. econstructor; eauto.
        + eapply elem_of_dom_2; eauto.  
    Qed. 
    
  End TlExtTrans.  


  Section ProgressProperties.

    Let ExtTL := ext_model tl_fair_model _ _ tl_active_exts_spec. 

    Section ProgressPropertiesImpl.

      Context (tr: mtrace ExtTL).
      Context (len: my_omega.nat_omega) (LEN: trace_len_is tr len).
      Hypothesis (VALID: mtrace_valid tr).
      Hypothesis (FROM_INIT: exists n, tr S!! 0 = Some (tl_init_st n)). 
      Hypothesis (FAIR: set_fair_model_trace (fun (ρ: fmrole ExtTL) => 
                                                exists r, ρ = inl r) tr).
      
      Local Ltac gd t := generalize dependent t.
      (* Lemma lock_role_stays_enabled_step ρ i st ρ' st' *)
      (*   (ITH: mtrace_nth tr i = Some st) *)
      (*   (RMρ: role_map st !! ρ = Some (tl_L, e)) *)
      (*   (OTHER: ρ' ≠ ρ) *)
      
      Definition role_state_kept (P: tl_role_st -> Prop) :=
        forall st ρ s (RMρ: role_map st !! ρ = Some s) (Ps: P s),      
        forall st' (oeρ: option (fmrole ExtTL)) (OTHER: oeρ ≠ Some (inl ρ))
          (STEP: fmtrans ExtTL st oeρ st'),
        ∃ s', role_map st' !! ρ = Some s' /\ P s'.

      Lemma lock_compete_kept: role_state_kept (eq (tl_L, true)).
      Proof using. 
        red. intros.
        exists (tl_L, true). split; auto.
        inversion STEP; subst.
        - assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; auto. 
          all: try by rewrite lookup_insert_ne; auto.
          subst st''. rewrite /advance_next. 
          destruct (role_of_dec _ _); simpl.
          2: { rewrite lookup_insert_ne; auto. }
          destruct s; simpl.
          rewrite lookup_insert_ne.
          { rewrite lookup_insert_ne; auto. }
          intros ->. subst st'0 st'1. simpl in *. 
          rewrite lookup_insert_ne in e; auto.
          rewrite RMρ in e. congruence.
        - destruct ι; inversion REL; subst; simpl in *.
          all: rewrite lookup_insert_ne; auto; 
            intros ->; rewrite RMρ in LOCK; congruence.
      Qed.
      
      (* From Paco Require Import pacotac. *)
      Lemma mtrace_valid_steps' i st ℓ st'
        (ITH: tr !! i = Some (st, Some (ℓ, st'))):
        fmtrans _ st ℓ st'. 
      Proof using.
        generalize dependent st. generalize dependent ℓ. generalize dependent st'. 
        induction i.
        (* { simpl. intros. punfold VALID. inversion VALID; subst; congruence. } *)
        (* intros. *)
      Admitted.
      
      (* Lemma owner_le_ticket i st (ITH: tr S!! i = Some st): *)
      (*   owner st <= ticket st.  *)
      (* Proof using.  *)
      (*   gd st. induction i.  *)
      (*   { intros. destruct FROM_INIT as [n INIT]. rewrite ITH in INIT. *)
      (*     rewrite /tl_init_st in INIT. inversion INIT. subst. simpl. lia. } *)
      (*   rewrite -Nat.add_1_r. intros st' ITH'.  *)
      (*   forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto. *)
      (*   specialize_full ITH; [eapply state_lookup_dom; eauto| ]. desc. *)
      (*   pose proof (mtrace_valid_steps' _ _ _ _ ITH) as STEP. *)
      (*   apply state_label_lookup in ITH. desc. *)
      (*   specialize (IHi _ ITH).  *)
      (*   rewrite ITH0 in ITH'. inversion ITH'. subst. clear ITH'. *)
      (*   inversion STEP; subst. *)
      (*   2: { destruct ι; simpl in *; inversion REL; subst; auto. } *)
      (*   inversion STEP0; subst; simpl in *. *)
      (*   all: try by lia. *)
      (*   subst st'' st'0. rewrite /advance_next. simpl.  *)

      
      (* Lemma tickets_bound o t (rm: tl_role_map) *)
      (*   (TKS: forall k, o <= k < t <-> *)
      (*                (exists ρ e, rm !! ρ = Some (tl_U k, e) /\ *)
      (*                          (o < k -> e = true))): *)
      (*   forall ρ k e, rm !! ρ = Some (tl_U k, e) -> o <= k < t. *)
      (* Proof using.  *)
      (*   intros.  *)


      (* Lemma disabled_unlock_owner o t (rm: tl_role_map) *)
      (*   (TKS: forall k, o <= k < t <-> *)
      (*                (exists ρ e, rm !! ρ = Some (tl_U k, e) /\ *)
      (*                          (o < k -> e = true))): *)
      (*     forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o. *)
      (* Proof using. *)
      (*   intros. specialize (TKS k). *)
      (*   destruct (Nat.lt_trichotomy k o) as [LT | [? | GT]]; auto. *)
      (*   - apply not_iff_compat, proj1 in TKS. specialize_full TKS; [lia| ]. *)
      (*     destruct TKS. do 2 eexists. split; eauto. lia. *)
      (*   - apply proj1 in TKS. specialize_full TKS; [lia| ]. *)
      
      Lemma ticket_numbers o t (rm: tl_role_map)
        (TKo: o < t <-> exists ρ e, rm !! ρ = Some (tl_U o, e))
        (TKs: forall k, o < k < t <-> exists ρ, rm !! ρ = Some (tl_U k, true)):
        forall k, o <= k < t <->exists ρ e, rm !! ρ = Some (tl_U k, e).
      Proof using. 
        intros. split.
        - intros [[GT | ->]%Nat.le_lteq LT].
          + specialize (TKs k) as [TKs _]. 
            specialize_full TKs; [lia| ]. desc. eauto.
          + apply proj1 in TKo. specialize (TKo LT). eauto.
        - intros (ρ & e & RMρ).
      Abort. 
          
          

      (* Lemma tl_valid_trace_states i o t rm (ITH: tr S!! i = Some <{o, t, rm}>): *)
      (*   o <= t /\ *)
      (*   (* (forall k, o <= k < t <->  *) *)
      (*   (*       (exists ρ e, rm !! ρ = Some (tl_U k, e) /\  *) *)
      (*   (*               (o < k -> e = true))) /\ *) *)
      (*   (o < t <-> exists ρ e, rm !! ρ = Some (tl_U o, e)) /\ *)
      (*   (forall k, o < k < t <-> exists ρ, rm !! ρ = Some (tl_U k, true)) /\ *)
      (*   (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))  *)
      (*      (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2) *)
      (*        (* exists ρ, (unique (fun ρ_ => exists e, rm !! ρ_ = Some (tl_U k, e)) ρ) /\ *) *)
      (*        (*      (o < k -> rm !! ρ = Some (tl_U k, true)). *) *)
      (*     (* TODO: add uniqueness condition? *) *)
      (*     .  *)
      (* Proof using.  *)
      (*   gd o. gd t. gd rm. induction i. *)
      (*   { intros. destruct FROM_INIT as [n INIT]. rewrite ITH in INIT. *)
      (*     rewrite /tl_init_st in INIT. inversion INIT. subst. *)
      (*     splits; auto. *)
      (*     - split; [lia| ]. intros. desc. *)
      (*       rewrite lookup_gset_to_gmap_Some in H. desc. congruence.   *)
      (*     - split; [lia| ]. intros [ρ RMρ]. desc. *)
      (*       apply lookup_gset_to_gmap_Some in RMρ. desc. congruence. *)
      (*     - intros. desc. rewrite lookup_gset_to_gmap_Some in R1. by desc. } *)
      (*   intros rm' t' o'. rewrite -Nat.add_1_r. intros ITH'. *)
      (*   forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto. *)
      (*   specialize_full ITH; [eapply state_lookup_dom; eauto| ]. desc. *)
      (*   pose proof (mtrace_valid_steps' _ _ _ _ ITH) as STEP. *)
      (*   apply state_label_lookup in ITH. desc. *)
      (*   rewrite ITH' in ITH0. inversion ITH0. subst. clear ITH0. *)
      (*   destruct st as [o t rm]. *)
      (*   specialize (IHi _ _ _ ITH) as (IHle & IHtko & IHtks & IHuniq). *)
      (*   inversion STEP; subst. *)
      (*   - inversion STEP0; subst; simpl in *; auto.  *)
      (*     + rename o' into o.  *)
      (*       splits; [lia| ..]. *)
      (*       { split; [| lia]. intros _. *)
      (*         apply le_lt_eq_dec in IHle as [LTot | ->]. *)
      (*         - apply proj1 in IHtko. specialize (IHtko LTot). desc. *)
      (*           exists ρ0, e. rewrite lookup_insert_ne; eauto. congruence.  *)
      (*         - exists ρ. eexists. rewrite lookup_insert. eauto. } *)
      (*       2: { intros. *)
      (*            destruct (decide (ρ1 = ρ)) as [-> | ?]. *)
      (*            - rewrite lookup_insert in R1. inversion R1. subst. *)
      (*              destruct (decide (ρ2 = ρ)) as [-> | ?]. *)
      (*              + done. *)
      (*              + rewrite lookup_insert_ne in R2; auto. *)
      (*                rename k into t.  *)
      (*                enough (t < t); [lia| ]. apply IHtks. *)
      (*                (* destruct (decide (o = t)); [lia| ]. subst next_en0. *) *)
 
      (*                do 2 eexists. split; eauto. *)
      (*                intros.  *)
      (*                eapply IHuniq;   *)
      (*                foobar. move e = true condition outside of <-> ?  *)
      (*                congruence.   *)
      (*       intros. *)
      (*       specialize (IHtks k). *)
      (*       destruct (decide (k = t)) as [-> | NEQ]. *)
      (*       * split; [| lia]. *)
      (*         intros T. exists ρ. eexists. rewrite lookup_insert. split; eauto.  *)
      (*         destruct (decide (o' = t)); [lia|]. auto. *)
      (*       * etransitivity. *)
      (*         { etransitivity; [| apply IHtks]. lia. }               *)
      (*         split; intros; desc. *)
      (*         ** do 2 eexists. split; [| apply H0].  *)
      (*            rewrite lookup_insert_ne; eauto. *)
      (*            intros <-. congruence. *)
      (*         ** do 2 eexists. split; [| apply H0]. *)
      (*            rewrite <- H. symmetry. apply lookup_insert_ne.  *)
      (*            intros <-. rewrite lookup_insert in H. congruence. *)
      (*      + subst st'3 st'' st'. rewrite /advance_next in H4. simpl in *. *)
      (*        assert (o' = o + 1 /\ t' = t) as [-> ->]. *)
      (*        { destruct (role_of_dec _ _) as [[? ?] | ?] ; by inversion H4. } *)
      (*        destruct (decide (o = t)) as [<- | NEQ]. *)
      (*        { specialize (IHtks o). apply proj2 in IHtks.  *)
      (*          destruct IHtks; [eauto | lia]. } *)
      (*        split; [lia| ]. *)
      (*        intros. specialize (IHtks k). *)
      (*        destruct (decide (k = o)) as [-> | NEQko]. *)
      (*        { split; intros; [lia| ]. desc. lia.  *)



      (*        etransitivity; [| etransitivity]; [| apply IHtks|]. *)
      (*        {  *)


      (* Admitted.  *)

      Lemma advance_next_helper_L o t (rm: tl_role_map) ρo ρ:
        role_map (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_L, false) <-> (rm !! ρ = Some (tl_L, false) \/ ρ = ρo).
      Proof using.      
        rewrite /advance_next.
        destruct role_of_dec as [[? ?] | ?]; simpl in *.
        - assert (x ≠ ρo) as NEQ.
          { intros ->. rewrite lookup_insert in e. congruence. }
          rewrite lookup_insert_ne in e; auto.
          destruct (decide (x = ρ)) as [-> | NEQ'].
          { rewrite lookup_insert. split; [congruence| ].
            intros [? | ->]; try congruence. rewrite e in H. congruence. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert. tauto. }
          rewrite lookup_insert_ne; auto. split; auto.
          intros [? | ?]; done.
        - destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert. tauto. }
          rewrite lookup_insert_ne; auto. split; auto.
          intros [? | ?]; done.
      Qed. 

      Lemma advance_next_helper_U o t (rm: tl_role_map) ρo ρ k b
        (RMρo: rm !! ρo = Some (tl_U o, true))
        (UNIQ: forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
                 (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2)
        (TKo: forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o):
        role_map (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_U k, b) <-> (exists b', rm !! ρ = Some (tl_U k, b') /\ 
                    (k = o + 1 /\ b = false /\ b' = true \/
                     k ≠ o /\ k ≠ (o + 1) /\ b' = b)). 
      Proof using.
        rewrite /advance_next.
        destruct role_of_dec as [[? ?] | ?]; simpl in *.
        - assert (x ≠ ρo) as NEQ.
          { intros ->. rewrite lookup_insert in e. congruence. }
          rewrite lookup_insert_ne in e; auto.
          destruct (decide (x = ρ)) as [-> | NEQ'].
          { rewrite lookup_insert. split.
            - intros. inversion H. eexists. eauto.
            - intros. desc. destruct H0; desc; subst; rewrite e in H; congruence. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite lookup_insert. rewrite RMρo. split; intros; desc. 
            - congruence.
            - destruct H0; desc; subst.
              + inversion H. lia.
              + congruence. }
          rewrite lookup_insert_ne; auto. split; intros; desc.
          + exists b. split; auto. right. splits; auto; intros ->.
            * destruct NEQ''. eapply UNIQ; eauto.
            * destruct NEQ'. eapply UNIQ; eauto.
          + rewrite H. repeat f_equal. destruct H0; desc; subst; auto.
            destruct NEQ'. eapply UNIQ; eauto. 
        - destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert.
            rewrite RMρo. split; intros; desc; try congruence.
            destruct H0; desc; subst.
            - inversion H. lia.
            - congruence. } 
          rewrite lookup_insert_ne; auto. split; intros; desc; auto.
          + exists b. split; auto. right. splits; auto. 
            * intros ->. destruct NEQ''; eapply UNIQ; eauto.
            * intros ->. destruct b.
              ** destruct (n ρ). rewrite lookup_insert_ne; auto.
              ** apply TKo in H. lia.
          + destruct H0; desc; subst; auto.
            destruct (n ρ). rewrite lookup_insert_ne; auto.
      Qed. 


      Ltac simpl_li_eq := match goal with
                          | H: <[?x:=?y]> ?m !! ?x = ?r |- _
                            => rewrite lookup_insert in H
                          end.
      Ltac simpl_li_eq' := match goal with
                           | |- <[?x:=?y]> ?m !! ?x = ?r
                             => rewrite lookup_insert
                           end.
      
      Ltac simpl_li_neq := match goal with
                           | H: <[?x:=?y]> ?m !! ?x' = ?r, NE: ?x ≠ ?x' |- _ => 
                               rewrite lookup_insert_ne in H; [| by apply NE]
                           | H: <[?x:=?y]> ?m !! ?x' = ?r, NE: ?x' ≠ ?x |- _ =>
                               rewrite lookup_insert_ne in H;
                               [| by apply not_eq_sym; apply NE]
                           end.
      Ltac simpl_li_neq' := match goal with
                           | NE: ?x ≠ ?x' |- <[?x:=?y]> ?m !! ?x' = ?r => 
                               rewrite lookup_insert_ne; [| by apply NE]
                           | NE: ?x' ≠ ?x |- <[?x:=?y]> ?m !! ?x' = ?r => 
                               rewrite lookup_insert_ne;
                               [| by apply not_eq_sym; apply NE]
                           end.
      
      Ltac simpl_li := (repeat simpl_li_eq); (repeat simpl_li_neq);
                       (try simpl_li_eq'); (try simpl_li_neq'). 
      

      Lemma tl_valid_trace_states i o t rm (ITH: tr S!! i = Some <{o, t, rm}>):
        o <= t /\
        (forall k, o <= k < t <-> exists ρ e, rm !! ρ = Some (tl_U k, e)) /\
        (forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o) /\
        (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
           (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2)
             (* exists ρ, (unique (fun ρ_ => exists e, rm !! ρ_ = Some (tl_U k, e)) ρ) /\ *)
             (*      (o < k -> rm !! ρ = Some (tl_U k, true)). *)
          (* TODO: add uniqueness condition? *)
          .
      Proof using.
        gd o. gd t. gd rm. induction i.
        { intros. destruct FROM_INIT as [n INIT]. rewrite ITH in INIT.
          rewrite /tl_init_st in INIT. inversion INIT. subst.
          splits; auto.
          - split; [lia| ]. intros [ρ RMρ]. desc.
            apply lookup_gset_to_gmap_Some in RMρ. desc. congruence.
          - intros. rewrite lookup_gset_to_gmap_Some in H. by desc.
          - intros. rewrite lookup_gset_to_gmap_Some in R1. by desc. }

        intros rm' t' o'. rewrite -Nat.add_1_r. intros ITH'.
        forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto.
        specialize_full ITH; [eapply state_lookup_dom; eauto| ]. desc.
        pose proof (mtrace_valid_steps' _ _ _ _ ITH) as STEP.
        apply state_label_lookup in ITH. desc.
        rewrite ITH' in ITH0. inversion ITH0. subst. clear ITH0.
        destruct st as [o t rm].
        specialize (IHi _ _ _ ITH) as (IHle & IHtks & IHtko & IHuniq).
        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *; auto.
          + rename o' into o.
            splits; [lia| ..].
            * intros. specialize (IHtks k).
              destruct (decide (k = t)) as [-> | NEQ].
              { split; [| lia]. intros T.
                exists ρ. eexists. rewrite lookup_insert. split; eauto. }
              etransitivity.
              { etransitivity; [| apply IHtks]. lia. }
              split; intros; desc.
              ** do 2 eexists. rewrite lookup_insert_ne; eauto.
                 intros <-. congruence.
              ** do 2 eexists.
                 rewrite <- H. symmetry. apply lookup_insert_ne.
                 intros <-. rewrite lookup_insert in H. congruence.
            * intros.
              destruct (decide (ρ0 = ρ)) as [-> | NEQ].
              2: { rewrite lookup_insert_ne in H; eauto. } 
              rewrite lookup_insert in H. inversion H.
              subst k next_en0.
              destruct (decide (o = t)); congruence.
            * intros. destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              { congruence. }
              all: try (subst ρ1; rewrite lookup_insert in R1; inversion R1; subst k). 
              all: try (subst ρ2; rewrite lookup_insert in R2; inversion R2; subst k).
              all: try rewrite lookup_insert_ne in R1; auto.
              all: try rewrite lookup_insert_ne in R2; auto.
              1, 2: enough (t < t); [lia| ]; apply IHtks; by eauto.
              eapply IHuniq; eauto.
          + subst st'' st'3 st'2 st'0 st' st'1.
             assert (o' = o + 1 /\ t' = t) as [-> ->].
             { rewrite /advance_next in H4.
               destruct (role_of_dec _ _) as [[? ?] | ?]; by inversion H4. }
             apply Nat.le_lteq in IHle as [LT | ->].
             2: { enough (t < t); [lia| ]. apply IHtks. eauto. }
             splits; [lia| ..].
             * intros.


               rewrite /advance_next in H4.
               destruct (role_of_dec) as [[? ?] | ?]; simpl in *;
                 inversion H4; subst rm'; clear H4.
               ** destruct (decide (ρ = x)).
                  { subst x. rewrite lookup_insert in e. congruence. }
                  rewrite lookup_insert_ne in e; auto.
                  destruct (decide (k = o)) as [-> | NEQ].
                  { split; [lia| ]. intros (ρ' & e' & RMρ'). 
                    destruct (decide (ρ' = ρ)).
                    { subst ρ'. rewrite lookup_insert_ne in RMρ'; auto.
                      rewrite lookup_insert in RMρ'. congruence. }
                    destruct (decide (x = ρ')).
                    { subst x. rewrite lookup_insert in RMρ'.
                      inversion RMρ'. lia. }
                    rewrite !lookup_insert_ne in RMρ'; auto.
                    destruct n0. eapply IHuniq; eauto. }
                  etransitivity; [etransitivity| ]; [| by apply (IHtks k) |].
                  { lia. }
                  split.
                  *** intros. desc. 
                      destruct (decide (k = o + 1)).
                      **** subst. exists x, false. by rewrite lookup_insert.
                      **** exists ρ0, e0.
                           rewrite !lookup_insert_ne; [by apply H| ..].
                           { congruence. }
                           intros <-. rewrite e in H. congruence.
                  *** intros. desc.
                      destruct (decide (k = o + 1)).
                      **** subst. eauto.
                      **** destruct (decide (x = ρ0)) as [-> | ?].
                           { rewrite lookup_insert in H. congruence. }
                           rewrite lookup_insert_ne in H; auto.
                           destruct (decide (ρ = ρ0)) as [-> | ?].
                           { rewrite lookup_insert in H. congruence. }
                           rewrite lookup_insert_ne in H; auto.
                           eauto.
               ** specialize (IHtks k). 
                  split.
                  *** intros [GEk LTk].
                      apply proj1 in IHtks.
                      specialize_full IHtks; [lia| ]. desc.
                      do 2 eexists. rewrite lookup_insert_ne; eauto.
                      intros <-. rewrite R in IHtks.
                      inversion IHtks. lia.
                  *** intros. desc.
                      destruct (decide (ρ = ρ0)) as [-> | ?].
                      { rewrite lookup_insert in H. congruence. }
                      destruct (decide (k = o)) as [-> | NEQko].
                      **** rewrite lookup_insert_ne in H; auto. 
                           destruct n0. eapply IHuniq; eauto. 
                      **** enough (o <= k < t); [lia| ]. apply IHtks.
                           rewrite lookup_insert_ne in H; eauto.
             * intros. rewrite /advance_next in H4.
               destruct role_of_dec as [[? ?] | ?]; simpl in *; 
                 inversion H4; subst rm'; clear H4.
               ** destruct (decide (ρ0 = x)) as [-> | ?].
                  { rewrite lookup_insert in H. congruence. }
                  rewrite lookup_insert_ne in H; auto.
                  destruct (decide (x = ρ)) as [-> | ?].
                  { rewrite lookup_insert in e. congruence. }
                  rewrite lookup_insert_ne in e; auto.
                  destruct (decide (ρ0 = ρ)) as [-> | ?].
                  { rewrite lookup_insert in H. congruence. }
                  rewrite lookup_insert_ne in H; auto.
                  specialize (IHtko _ _ H). subst k.
                  destruct n1. eapply IHuniq; eauto.
               ** destruct (decide (ρ0 = ρ)) as [-> | ?].
                  { rewrite lookup_insert in H. congruence. }
                  rewrite lookup_insert_ne in H; auto. 
                  specialize (IHtko _ _ H). subst k.
                  destruct n0. eapply IHuniq; eauto.
             * intros.
               pose proof H4 as rm'_eq. apply (f_equal role_map) in rm'_eq. simpl in rm'_eq.
               rewrite -rm'_eq in R1 R2. 
               eapply advance_next_helper_U in R1, R2; auto. desc.
               destruct R0, R3; desc; subst.
               all: lia || eapply IHuniq; eauto.
        - destruct ι; simpl in REL; inversion REL; subst o0 t0 rm0 o' t' rm'.
          + split; auto. splits.
            * intros. etransitivity; [etransitivity|]; [| apply IHtks |]; [reflexivity|..].
              split; intros; desc.
              ** destruct (decide (ρ0 = ρ)) as [-> | NEQ].
                 *** exists ρ, true. rewrite lookup_insert. congruence.
                 *** exists ρ0, e. rewrite lookup_insert_ne; auto.
              ** destruct (decide (ρ0 = ρ)) as [-> | NEQ].
                 *** rewrite lookup_insert in H.
                     exists ρ, false. congruence.
                 *** rewrite lookup_insert_ne in H; auto.
                     eauto.
            * intros. eapply IHtko; eauto. rewrite -H.
              symmetry. apply lookup_insert_ne.
              intros ->. rewrite lookup_insert in H. congruence.
            * intros.
              destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              all: eapply IHuniq; eauto.
          + split; auto. splits.
            * intros. etransitivity; [etransitivity|]; [| apply IHtks |]; [reflexivity|..].
              split; intros; desc.
              ** exists ρ0, e. destruct (decide (ρ0 = ρ)); 
                   subst; simpl_li; [congruence| auto]. 
              ** destruct (decide (ρ0 = ρ)); subst; simpl_li; inversion H; eauto.
            * intros. destruct (decide (ρ0 = ρ)); subst; simpl_li; try congruence.
              eapply IHtko; eauto.
            * intros.
              destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              all: eapply IHuniq; eauto.
      Qed.


                 
              
                 



                          Lemma tl_valid_trace_states i o t rm (ITH: tr S!! i = Some <{o, t, rm}>):
        o <= t /\
        (forall k, o <= k < t <-> exists ρ e, rm !! ρ = Some (tl_U k, e)) /\
        (* (o < t <-> exists ρ e, rm !! ρ = Some (tl_U o, e)) /\ *)
        (* (forall k, o < k < t <-> exists ρ, rm !! ρ = Some (tl_U k, true)) /\ *)
        (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
           (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2)
             (* exists ρ, (unique (fun ρ_ => exists e, rm !! ρ_ = Some (tl_U k, e)) ρ) /\ *)
             (*      (o < k -> rm !! ρ = Some (tl_U k, true)). *)
          (* TODO: add uniqueness condition? *)
          .
      Proof using.
        gd o. gd t. gd rm. induction i.
        { intros. destruct FROM_INIT as [n INIT]. rewrite ITH in INIT.
          rewrite /tl_init_st in INIT. inversion INIT. subst.
          splits; auto.
          - split; [lia| ]. intros [ρ RMρ]. desc.
            apply lookup_gset_to_gmap_Some in RMρ. desc. congruence.
          - intros. desc. rewrite lookup_gset_to_gmap_Some in R1. by desc. }
        intros rm' t' o'. rewrite -Nat.add_1_r. intros ITH'.

        forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto.
        specialize_full ITH; [eapply state_lookup_dom; eauto| ]. desc.
        pose proof (mtrace_valid_steps' _ _ _ _ ITH) as STEP.
        apply state_label_lookup in ITH. desc.
        rewrite ITH' in ITH0. inversion ITH0. subst. clear ITH0.
        destruct st as [o t rm].
        specialize (IHi _ _ _ ITH) as (IHle & IHtks & IHuniq).
        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *; auto.
          + rename o' into o.
            splits; [lia| ..].
            2: { intros.
                 destruct (decide (ρ1 = ρ)) as [-> | ?].
                 - rewrite lookup_insert in R1. inversion R1. subst.
                   destruct (decide (ρ2 = ρ)) as [-> | ?].
                   + done.
                   + rewrite lookup_insert_ne in R2; auto.
                     rename k into t.
                     enough (t < t); [lia| ]. apply IHtks.
                     do 2 eexists. split; eauto.
                     intros. destruct (decide (o = t)); [lia| ]. subst next_en0.
                     
                     
                     destruct e2; auto.
                     specialize (IHtks o). apply proj1 in IHtks.
                     specialize_full IHtks; [lia| ].
                     eapply IHuniq;
                     foobar. move e = true condition outside of <-> ?
                     congruence.
            intros.
            specialize (IHtks k).
            destruct (decide (k = t)) as [-> | NEQ].
            * split; [| lia].
              intros T. exists ρ. eexists. rewrite lookup_insert. split; eauto.
              destruct (decide (o' = t)); [lia|]. auto.
            * etransitivity.
              { etransitivity; [| apply IHtks]. lia. }
              split; intros; desc.
              ** do 2 eexists. split; [| apply H0].
                 rewrite lookup_insert_ne; eauto.
                 intros <-. congruence.
              ** do 2 eexists. split; [| apply H0].
                 rewrite <- H. symmetry. apply lookup_insert_ne.
                 intros <-. rewrite lookup_insert in H. congruence.
           + subst st'3 st'' st'. rewrite /advance_next in H4. simpl in *.
             assert (o' = o + 1 /\ t' = t) as [-> ->].
             { destruct (role_of_dec _ _) as [[? ?] | ?] ; by inversion H4. }
             destruct (decide (o = t)) as [<- | NEQ].
             { specialize (IHtks o). apply proj2 in IHtks.
               destruct IHtks; [eauto | lia]. }
             split; [lia| ].
             intros. specialize (IHtks k).
             destruct (decide (k = o)) as [-> | NEQko].
             { split; intros; [lia| ]. desc. lia.



             etransitivity; [| etransitivity]; [| apply IHtks|].
             {


      Admitted.




      Lemma steps_keep_state ρ (i: nat) (P: tl_role_st -> Prop) (j: nat)
        (Pi: exists st s, tr S!! i = Some st /\ role_map st !! ρ = Some s /\ P s)
        (DOMj: my_omega.NOmega.lt_nat_l j len)
        (P_KEPT: role_state_kept P)
        (NOρ: forall (k: nat) ℓ (IKJ: i <= k < j),
            tr L!! k = Some ℓ -> ℓ ≠ Some (inl ρ)):
        forall (k: nat) (IKJ: i <= k <= j), 
        exists st s, tr S!! k = Some st /\ role_map st !! ρ = Some s /\ P s.
      Proof using VALID LEN. 
        intros k [IK KJ]. apply Nat.le_sum in IK as [d ->]. induction d.
        { by rewrite Nat.add_0_r. }
        specialize_full IHd; [lia| ]. desc.
        forward eapply (proj2 (trace_lookup_dom_strong  _ _ LEN (i + d))) as [st_ CUR].
        { destruct len; auto. simpl in *. lia. }
        desc. apply state_label_lookup in CUR. desc.
        assert (st_ = st) as -> by congruence.
        red in P_KEPT. specialize (P_KEPT _ _ _ IHd0 IHd1). specialize_full P_KEPT.
        2: { eapply mtrace_valid_steps'. apply state_label_lookup. eauto. }
        { eapply NOρ; eauto. lia. }
        rewrite Nat.add_succ_r -Nat.add_1_r.
        desc. eauto. 
      Qed.
      
      Lemma lock_eventually_acquired o t rm ρ i wt 
        (ST: tr S!! i = Some <{ o, t, rm }>)
        (WAIT: o ≠ wt)
        (R: rm !! ρ = Some (tl_U wt, true)):
        ∃ (n : nat) (st' : tl_st),
          i < n ∧ tr S!! n = Some st' ∧ has_lock_st ρ st' ∧ ¬ active_st ρ st'.
      Proof using.
        (* red in WAIT. apply Nat.le_sum in WAIT as [d ->]. *)
        (* gd o. gd t. gd i. gd rm. *)
        (* induction d. *)
        (* { intros. rewrite Nat.add_0_r in R. *)
        
      Admitted. 

      Theorem tl_progress ρ i st
        (ITH: tr S!! i = Some st)
        (CAN_LOCK: can_lock_st ρ st)
        (ACT: active_st ρ st)
        (EV_REL: forall ρ' j st' (JTH: tr S!! j = Some st')
                   (HAS_LOCK: has_lock_st ρ' st')
                   (PREVr: ρ' = ρ -> j < i),
          exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''):
        exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\
                   ¬ active_st ρ st'.
      Proof using VALID LEN FAIR.
        red in CAN_LOCK. destruct CAN_LOCK as [e RMρ].
        assert (e = true) as -> by (destruct ACT; congruence). 
        pose proof (FAIR (inl ρ)) as FAIRρ. specialize_full FAIRρ; [by eauto| ].  
        apply fair_model_trace_defs_equiv, strong_fair_model_trace_alt_defs_equiv in FAIRρ. 
        red in FAIRρ. edestruct FAIRρ as [d [STEP MIN]]; [eauto| ..].
        { red. simpl. simpl. rewrite /ext_live_roles.
          apply elem_of_union_l. apply gset_map_in.
          by apply active_st_enabled. }
        clear FAIRρ. 

        assert (my_omega.NOmega.lt_nat_l (i + d) len) as DOMid.
        { destruct STEP; desc.
          - eapply state_lookup_dom; eauto.
          - apply my_omega.NOmega.lt_lt_nat with (m := i + d + 1); [lia| ].
            eapply label_lookup_dom; eauto. } 

        forward eapply steps_keep_state with (j := i + d) (k := i + d) as NEXT_EN.
        3: { apply lock_compete_kept. }
        { eauto. }
        3: { lia. }
        { auto. }
        { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ]. 
          intros ->. enough (d <= v); [lia| ]. apply MIN. eauto. }
        desc. subst. rename st0 into st'. 
        
        destruct STEP as [(st'_ & ST' & DIS') | STEP].
        { assert (st'_ = st') as -> by congruence. 
          destruct DIS'. red. simpl.
          rewrite /ext_live_roles. apply elem_of_union_l. apply gset_map_in.
          simpl. rewrite /tl_live_roles.
          apply elem_of_dom. eexists. apply map_filter_lookup_Some_2; done. }

        forward eapply (proj1 (label_lookup_states tr (i + d))) as [_ [st'' ST''']]; eauto.
        forward eapply (mtrace_valid_steps' (i + d)) as TRANS.
        { eapply state_label_lookup; eauto. }
        simpl in TRANS. inversion TRANS as [? ? ? TRANS'| ]; subst.
        inversion TRANS'; subst; simpl in *.
        all: try by rewrite NEXT_EN0 in R.
        destruct (decide (o = t)) as [<- | WAIT]. 
        { exists (i + d + 1). eexists. splits; [lia|..]; try by eauto.
          - red. eexists. simpl. rewrite lookup_insert. eauto. 
          - rewrite /active_st. simpl. rewrite lookup_insert. intros [? [=]]. }

        (* eapply lock_eventually_acquired.  *)
        eapply lock_eventually_acquired in ST'''.
        - desc. do 2 eexists. splits.
          2-4: by eauto. lia. 
        - apply WAIT. 
        - rewrite lookup_insert. eauto. 
      Qed. 

    End ProgressPropertiesImpl. 

      
  End ProgressProperties. 

End Model.
                       

From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness trace_utils trace_lookup.

Section fairness.
  Context {G: Type}.
  Context {M: FairModel}.
  Context `{Countable G}.
  Context {LSI: fmstate M -> gmap M.(fmrole) G -> gmap M.(fmrole) nat -> Prop}.
  Context `{forall s m f, Decision (LSI s m f)}.

  Record LiveState := MkLiveState {
    ls_under:> M.(fmstate);

    ls_fuel: gmap M.(fmrole) nat;
    ls_fuel_dom: M.(live_roles) ls_under ⊆ dom ls_fuel;

    ls_mapping: gmap M.(fmrole) G;

    ls_same_doms: dom ls_mapping = dom ls_fuel;

    ls_inv: LSI ls_under ls_mapping ls_fuel;
  }.

  Arguments ls_under {_}.
  Arguments ls_fuel {_}.
  Arguments ls_fuel_dom {_}.
  Arguments ls_mapping {_}.
  Arguments ls_same_doms {_}.

  Lemma ls_mapping_dom (m: LiveState):
    M.(live_roles) m.(ls_under) ⊆ dom m.(ls_mapping).
  Proof. rewrite ls_same_doms. apply ls_fuel_dom. Qed.

  Inductive FairLabel {Roles} :=
  | Take_step: Roles -> G -> FairLabel
  | Silent_step: G -> FairLabel
  | Config_step: FairLabel
  .
  Arguments FairLabel : clear implicits.

  Global Instance FL_eqdec: EqDecision (@FairLabel (fmrole M)).
  Proof. solve_decision. Qed.

  Global Instance FL_cnt: Countable (@FairLabel (fmrole M)).
  Proof. 
    set (FL_alt := (G * (fmrole M) + G + unit)%type).
    set (to_alt := fun fl => match fl with
                          | Take_step ρ τ => inl $ inl (τ, ρ)
                          | Silent_step τ => inl $ inr τ
                          | Config_step => (inr tt): FL_alt
                          end).
    set (from_alt := fun (fl': FL_alt) => match fl' with
                             | inl (inl (τ, ρ)) => Take_step ρ τ
                             | inl (inr τ) => Silent_step τ
                             | inr _ => Config_step
                             end).
    eapply (inj_countable' to_alt from_alt).
    intros. by destruct x. 
  Qed. 

  Definition less (x y: option nat) :=
    match x, y with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Inductive must_decrease (ρ': M.(fmrole)) (oρ: option M.(fmrole)) (a b: LiveState):
    option G -> Prop :=
  | Same_tid tid (Hneqρ: Some ρ' ≠ oρ) (Hsametid: Some tid = a.(ls_mapping) !! ρ'):
      must_decrease ρ' oρ a b (Some tid)
  | Change_tid otid (Hneqtid: a.(ls_mapping) !! ρ' ≠ b.(ls_mapping) !! ρ')
               (Hissome: is_Some (b.(ls_mapping) !! ρ')):
    must_decrease ρ' oρ a b otid
  (* | Zombie otid (Hismainrole: oρ = Some ρ') (Hnotalive: ρ' ∉ live_roles _ b) (Hnotdead: ρ' ∈ dom b.(ls_fuel)): *)
  (*   must_decrease ρ' oρ a b otid *)
  .

  Global Instance must_decrease_dec:
    forall a oρ st1 st2 og, Decision (must_decrease a oρ st1 st2 og).
  Proof. 
    intros.
    destruct (decide (@ls_mapping st1 !! a ≠ @ls_mapping st2 !! a /\ is_Some (@ls_mapping st2 !! a))).
    { left. apply Change_tid; apply a0. }
    destruct og.
    2: { right. intros DECR. inversion DECR; tauto. }
    destruct (decide (Some a ≠ oρ /\ Some g = @ls_mapping st1 !! a)).
    - left. econstructor; apply a0.
    - right. intros DECR. inversion DECR; tauto.
  Qed.


  Definition fuel_decr (tid: option G) (oρ: option M.(fmrole))
             (a b: LiveState) :=
    ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> ρ' ∈ dom b.(ls_fuel) →
          must_decrease ρ' oρ a b tid ->
          oless (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ').

  Definition fuel_must_not_incr oρ (a b: LiveState) :=
    (* ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> Some ρ' ≠ oρ -> *)
    (*       (oleq (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ') *)
    (*             ∨ (ρ' ∉ dom b.(ls_fuel) ∧ ρ' ∉ M.(live_roles) a.(ls_under))). *)
    ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> 
          (oleq (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ') ∨
           oρ = Some ρ' /\ (ρ' ∉ dom b.(ls_fuel) \/ ρ' ∈ M.(live_roles) b.(ls_under)) \/
           (ρ' ∉ dom b.(ls_fuel) ∧ ρ' ∉ M.(live_roles) a.(ls_under))).

  Definition ls_trans fuel_limit (a: LiveState) ℓ (b: LiveState): Prop :=
    match ℓ with
    | Take_step ρ tid =>
      M.(fmtrans) a (Some ρ) b
      ∧ a.(ls_mapping) !! ρ = Some tid
      ∧ fuel_decr (Some tid) (Some ρ) a b
      ∧ fuel_must_not_incr (Some ρ) a b
      ∧ (ρ ∈ live_roles _ b -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ (∀ ρ, ρ ∈ dom b.(ls_fuel) ∖ dom a.(ls_fuel) -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ dom b.(ls_fuel) ∖ dom a.(ls_fuel) ⊆ live_roles _ b ∖ live_roles _ a
    | Silent_step tid =>
      (∃ ρ, a.(ls_mapping) !! ρ = Some tid)
      ∧ fuel_decr (Some tid) None a b
      ∧ fuel_must_not_incr None a b
      ∧ dom b.(ls_fuel) ⊆ dom a.(ls_fuel)
      ∧ a.(ls_under) = b.(ls_under)
    | Config_step =>
      M.(fmtrans) a None b
      ∧ fuel_decr None None a b
      ∧ fuel_must_not_incr None a b
      ∧ (∀ ρ, ρ ∈ M.(live_roles) b ∖ M.(live_roles) a -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ False (* TODO: add support for config steps later! *)
    end.

  Record LiveModel := {
      lm_fl : M → nat;
      lm_ls := LiveState;
      lm_lbl := FairLabel M.(fmrole);
      lm_ls_trans := ls_trans lm_fl;
    }.
  
  Definition fair_lbl_matches_group (ℓ: @FairLabel (fmrole M)) (τ: G) := 
    match ℓ with
    | Take_step _ τ' | Silent_step τ' => τ = τ'
    | Config_step => False
    end. 

  Global Instance fair_lbl_match_Dec: 
    forall ℓ τ, Decision (fair_lbl_matches_group ℓ τ).
  Proof.
    intros. destruct ℓ; simpl; solve_decision.
  Qed.  

  Definition live_model_model `(LM : LiveModel) : Model := {|
    mstate := lm_ls LM;
    mlabel := lm_lbl LM;
    mtrans := lm_ls_trans LM;
  |}.

  Lemma ls_same_doms' (δ: LiveState):
    forall ρ, is_Some (@ls_mapping δ !! ρ) <-> is_Some (@ls_fuel δ !! ρ).
  Proof. 
    intros. rewrite -!elem_of_dom. by rewrite ls_same_doms.
  Qed.

  Program Definition initial_ls `{LM: LiveModel} (s0: M) (ζ0: G)
    (f0 := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0))
    (m0 := gset_to_gmap ζ0 (M.(live_roles) s0))
    (LSI0: LSI s0 m0 f0) 
    : LM.(lm_ls) :=
    {| ls_under := s0;
       ls_fuel := f0;
       ls_mapping := m0;
    |}.
  Next Obligation. 
    simpl. intros. apply reflexive_eq. rewrite dom_gset_to_gmap //.
  Qed.
  Next Obligation. 
    simpl. intros. apply reflexive_eq. rewrite !dom_gset_to_gmap //. 
  Qed.
  Next Obligation.
    done.
  Qed. 

  Local Ltac SS' := eapply elem_of_dom; eauto. 

  Lemma others_step_fuel_decr `{LM: LiveModel} ρ f f' τ δ ℓ δ'
    (STEP: lm_ls_trans LM δ ℓ δ')
    (Hfuel : @ls_fuel δ !! ρ = Some f)
    (Hmapping : @ls_mapping δ !! ρ = Some τ)
    (Hζ: ¬ fair_lbl_matches_group ℓ τ)
    (FUEL: @ls_fuel δ' !! ρ = Some f'):
    f' ≤ f.
  Proof.
    simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
    + destruct STEP as (?&?&?&Hnoninc&?).
      unfold fuel_must_not_incr in Hnoninc.
      have Hneq: Some ρ ≠ Some ρ0 by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc.
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver. 
    + destruct STEP as (?&?&Hnoninc&?).
      unfold fuel_must_not_incr in Hnoninc.
      have Hneq: Some ρ ≠ None by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc. 
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver.
    + destruct STEP as [_ [_ [Hnoninc _]]].
      have HnotNone: Some ρ ≠ None by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc. 
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver.
  Qed. 
  
  Lemma owner_change_fuel_decr `{LM: LiveModel} ρ f f'
    δ ℓ δ'
    τ τ''
    (STEP: lm_ls_trans LM δ ℓ δ')
    (Hfuel: @ls_fuel δ !! ρ = Some f)
    (Hmapping: @ls_mapping δ !! ρ = Some τ)
    (Hζ'' : @ls_mapping δ' !! ρ = Some τ'')
    (Hchange : τ ≠ τ'')
    (FUEL: @ls_fuel δ' !! ρ = Some f'):
    f' < f.
  Proof.
    destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
    + destruct STEP as (?&?&Hdec&?&?).
      unfold fuel_decr in Hdec. simplify_eq.
      have Hmd: must_decrease ρ (Some ρ0) δ δ' (Some ζ0).
      { econstructor 2. congruence. rewrite Hζ''; eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec. 
    + destruct STEP as (?&Hdec&_).
      unfold fuel_decr in Hdec. simplify_eq.
      have Hmd: must_decrease ρ None δ δ' (Some ζ0).
      { econstructor 2. congruence. rewrite Hζ''; eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec.
    + destruct STEP as [_ [Hdec _]].
      unfold fuel_decr in Hdec.
      have Hmd: must_decrease ρ None δ δ' None.
      { econstructor. congruence. rewrite Hζ''. eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec.
  Qed.

End fairness.

Arguments LiveState : clear implicits.
Arguments LiveModel : clear implicits.
Arguments live_model_model _ {_} _ _.

Definition live_model_to_model : forall G M LSI, LiveModel G M LSI -> Model :=
  λ G M LSI lm, live_model_model G LSI lm.
Coercion live_model_to_model : LiveModel >-> Model.
Arguments live_model_to_model {_ _}.



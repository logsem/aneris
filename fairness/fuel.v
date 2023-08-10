From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness.

Section fairness.
  Context {G: Type}.
  Context {M: FairModel}.
  Context `{Countable G}.

  Record LiveState := MkLiveState {
    ls_under:> M.(fmstate);

    ls_fuel: gmap M.(fmrole) nat;
    ls_fuel_dom: M.(live_roles) ls_under ⊆ dom ls_fuel;

    ls_mapping: gmap M.(fmrole) G;

    ls_same_doms: dom ls_mapping = dom ls_fuel;
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
  
  Definition fair_model_model `(LM : LiveModel) : Model := {|
    mstate := lm_ls LM;
    mlabel := lm_lbl LM;
    mtrans := lm_ls_trans LM;
  |}.

  Program Definition initial_ls `{LM: LiveModel} (s0: M) (ζ0: G)
    : LM.(lm_ls) :=
    {| ls_under := s0;
       ls_fuel := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0);
       ls_mapping := gset_to_gmap ζ0 (M.(live_roles) s0);
    |}.
  Next Obligation. intros ???. apply reflexive_eq. rewrite dom_gset_to_gmap //. Qed.
  Next Obligation. intros ???. apply reflexive_eq. rewrite !dom_gset_to_gmap //. Qed.

End fairness.

Arguments LiveState : clear implicits.
Arguments LiveModel : clear implicits.
Arguments fair_model_model _ {_} _.

Definition live_model_to_model : forall G M, LiveModel G M -> Model :=
  λ G M lm, fair_model_model G lm.
Coercion live_model_to_model : LiveModel >-> Model.
Arguments live_model_to_model {_ _}.


Section aux_trace.  
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{Countable (locale Λ)}.

  Notation "'Tid'" := (locale Λ). 

  Definition auxtrace := trace LM.(lm_ls) LM.(lm_lbl).

  Definition tids_smaller (c : list (expr Λ)) (δ: LiveState Tid M) :=
    ∀ ρ ζ, δ.(ls_mapping) !! ρ = Some ζ -> is_Some (from_locale c ζ).

  Definition labels_match (oζ : option Tid) (ℓ : LM.(lm_lbl)) : Prop :=
    match oζ, ℓ with
    | None, Config_step => True
    | Some ζ, Silent_step ζ' => ζ = ζ'
    | Some ζ, Take_step ρ ζ' => ζ = ζ'
    | _, _ => False
    end.

  Definition role_enabled ρ (δ: LiveState Tid M) := ρ ∈ M.(live_roles) δ.

  Definition fair_aux ρ (auxtr: auxtrace): Prop  :=
    forall n, pred_at auxtr n (λ δ _, role_enabled ρ δ) ->
         ∃ m, pred_at auxtr (n+m) (λ δ _, ¬role_enabled ρ δ)
              ∨ pred_at auxtr (n+m) (λ _ ℓ, ∃ tid, ℓ = Some (Take_step ρ tid)).

  Lemma fair_aux_after ρ auxtr n auxtr':
    fair_aux ρ auxtr ->
    after n auxtr = Some auxtr' ->
    fair_aux ρ auxtr'.
  Proof.
    rewrite /fair_aux => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p). by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp.
  Qed.

  CoInductive auxtrace_valid: auxtrace -> Prop :=
  | auxtrace_valid_singleton δ: auxtrace_valid ⟨δ⟩
  | auxtrace_valid_cons δ ℓ tr:
      LM.(lm_ls_trans) δ ℓ (trfirst tr) ->
      auxtrace_valid tr →
      auxtrace_valid (δ -[ℓ]-> tr).

  Lemma auxtrace_valid_forall (tr: auxtrace) :
    auxtrace_valid tr ->
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (δ -[ℓ]-> tr') => LM.(lm_ls_trans) δ ℓ (trfirst tr')
         end.
  Proof.
    intros Hval n. revert tr Hval. induction n as [|n]; intros tr Hval;
      destruct (after _ tr) as [trn|] eqn: Heq =>//; simpl in Heq;
      simplify_eq; destruct trn =>//; inversion Hval; simplify_eq; try done.
    specialize (IHn _ H1) (* TODO *). rewrite Heq in IHn. done.
  Qed.

End aux_trace.

Ltac SS :=
  epose proof ls_fuel_dom;
  (* epose proof ls_mapping_dom; *)
  set_solver.

Definition live_tids `{LM:LiveModel (locale Λ) M} `{EqDecision (locale Λ)}
           (c : cfg Λ) (δ : LM.(lm_ls)) : Prop :=
  (∀ ρ ζ, δ.(ls_mapping (G := locale Λ)) !! ρ = Some ζ -> is_Some (from_locale c.1 ζ)) ∧
  ∀ ζ e, from_locale c.1 ζ = Some e -> (to_val e ≠ None) ->
         ∀ ρ, δ.(ls_mapping) !! ρ ≠ Some ζ.

(* Definition exaux_traces_match `{LM:LiveModel (locale Λ) M} `{EqDecision (locale Λ)} : *)
(*   extrace Λ → auxtrace (LM := LM) → Prop := *)
(*   traces_match labels_match *)
(*                live_tids *)
(*                locale_step *)
(*                LM.(lm_ls_trans). *)


Definition valid_evolution_step `{LM:LiveModel (locale Λ) M} `{EqDecision (locale Λ)}
  oζ (σ2: cfg Λ) δ1 ℓ δ2 :=
    labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) δ1 ℓ δ2 ∧
    tids_smaller (σ2.1) δ2.

(* TODO: get rid of previous version *)
Definition lm_valid_evolution_step `{LM:LiveModel (locale Λ) M} `{EqDecision (locale Λ)}:
    cfg Λ → olocale Λ → cfg Λ → 
    mstate LM → lm_lbl LM → mstate LM -> Prop := 
    (fun (_: cfg Λ) => valid_evolution_step).

(* Section fairness_preserved. *)
(*   Context `{LM: LiveModel (locale Λ) M}. *)
(*   Context `{Countable (locale Λ)}. *)
(*   Notation "'Tid'" := (locale Λ).  *)

(*   Lemma exaux_preserves_validity extr (auxtr : auxtrace (LM := LM)): *)
(*     exaux_traces_match extr auxtr -> *)
(*     auxtrace_valid auxtr. *)
(*   Proof. *)
(*     revert extr auxtr. cofix CH. intros extr auxtr Hmatch. *)
(*     inversion Hmatch; first by constructor. *)
(*     constructor =>//. by eapply CH. *)
(*   Qed. *)

(*   Lemma exaux_preserves_termination extr (auxtr : auxtrace (LM := LM)) : *)
(*     exaux_traces_match extr auxtr -> *)
(*     terminating_trace auxtr -> *)
(*     terminating_trace extr. *)
(*   Proof. *)
(*     intros Hmatch [n HNone]. *)
(*     revert extr auxtr Hmatch HNone. induction n as [|n IHn]; first done. *)
(*     intros extr auxtr Hmatch HNone. *)
(*     replace (S n) with (1 + n) in HNone =>//. *)
(*     rewrite (after_sum' _ 1) in HNone. *)
(*     destruct auxtr as [s| s ℓ auxtr']; *)
(*       first by inversion Hmatch; simplify_eq; exists 1. *)
(*     simpl in HNone. *)
(*     inversion Hmatch; simplify_eq. *)
(*     apply terminating_trace_cons. *)
(*     eapply IHn =>//. *)
(*   Qed. *)

(*   Lemma traces_match_labels tid ℓ c δ rex (raux : auxtrace (LM := LM)) : *)
(*     exaux_traces_match (c -[Some tid]-> rex) (δ -[ℓ]-> raux) -> *)
(*     ((∃ ρ, ℓ = Take_step ρ tid) ∨ (ℓ = Silent_step tid)). *)
(*   Proof. *)
(*     intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq. *)
(*     destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto. *)
(*   Qed. *)

(*   Lemma mapping_live_role (δ: LiveState Tid M) ρ: *)
(*     ρ ∈ M.(live_roles) δ -> *)
(*     is_Some (ls_mapping (G := Tid) δ !! ρ). *)
(*   Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed. *)
(*   Lemma fuel_live_role (δ: LiveState Tid M) ρ: *)
(*     ρ ∈ M.(live_roles) δ -> *)
(*     is_Some (ls_fuel (G := Tid) δ !! ρ). *)
(*   Proof. rewrite -elem_of_dom. SS. Qed. *)

(*   Local Hint Resolve mapping_live_role: core. *)
(*   Local Hint Resolve fuel_live_role: core. *)

(*   Lemma match_locale_enabled (extr : extrace Λ) (auxtr : auxtrace (LM := LM)) ζ ρ: *)
(*     exaux_traces_match extr auxtr -> *)
(*     ls_mapping (trfirst auxtr) !! ρ = Some ζ -> *)
(*     locale_enabled ζ (trfirst extr). *)
(*   Proof. *)
(*     intros Hm Hloc. *)
(*     rewrite /locale_enabled. have [HiS Hneqloc] := traces_match_first _ _ _ _ _ _ Hm. *)
(*     have [e Hein] := (HiS _ _ Hloc). exists e. split; first done. *)
(*     destruct (to_val e) eqn:Heqe =>//. *)
(*     exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc. *)
(*     have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ). *)
(*   Qed. *)

(*   Local Hint Resolve match_locale_enabled: core. *)
(*   Local Hint Resolve pred_first_trace: core. *)

(*   Definition fairness_induction_stmt ρ fm f m ζ extr (auxtr : auxtrace (LM := LM)) *)
(*     δ c := *)
(*       (infinite_trace extr -> *)
(*        (forall ζ, fair_ex ζ extr) -> *)
(*        fm = (f, m) -> *)
(*        exaux_traces_match extr auxtr -> *)
(*        c = trfirst extr -> δ = trfirst auxtr -> *)
(*        δ.(ls_fuel) !! ρ = Some f -> *)
(*        δ.(ls_mapping) !! ρ = Some ζ -> *)
(*        (pred_at extr m (λ c _, ¬locale_enabled ζ c) ∨ pred_at extr m (λ _ oζ, oζ = Some (Some ζ))) -> *)
(*       ∃ M, pred_at auxtr M (λ δ _, ¬role_enabled ρ δ) *)
(*            ∨ pred_at auxtr M (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0))). *)

(*   Local Lemma case1 ρ f m (extr' : extrace Λ) (auxtr' : auxtrace (LM := LM)) δ ℓ : *)
(*     (∀ m0 : nat * nat, *)
(*          strict lt_lex m0 (f, m) *)
(*          → ∀ (f m: nat) (ζ: locale Λ) (extr : extrace Λ) (auxtr : auxtrace (LM := LM)) *)
(*              (δ : LiveState Tid M) (c : cfg Λ), fairness_induction_stmt ρ m0 f m ζ extr auxtr δ c) -> *)
(*     (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) -> *)
(*     exaux_traces_match extr' auxtr' -> *)
(*     infinite_trace extr' -> *)
(*     ls_fuel δ !! ρ = Some f -> *)
(*     (∀ ζ, fair_ex ζ extr') -> *)
(*     ∃ M0 : nat, *)
(*       pred_at (δ -[ ℓ ]-> auxtr') M0 *)
(*               (λ δ0 _, ¬ role_enabled ρ δ0) *)
(*       ∨ pred_at (δ -[ ℓ ]-> auxtr') M0 *)
(*                 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)). *)
(*     Proof. *)
(*       intros IH Hdec Hmatch Hinf Hsome Hfair. *)
(*       unfold oless in Hdec. *)
(*       simpl in *. *)
(*       rewrite -> Hsome in *. *)
(*       destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq. *)
(*       - destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first. *)
(*         { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. } *)
(*         have [ζ' Hζ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto. *)

(*         have Hloc'en: pred_at extr' 0 (λ (c : cfg Λ) (_ : option (olocale Λ)), *)
(*                           locale_enabled ζ' c). *)
(*         { rewrite /pred_at /= pred_first_trace. eauto. } *)

(*         have [p Hp] := (Hfair ζ' 0 Hloc'en). *)
(*         have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState Tid M) _, ¬ role_enabled ρ δ0) *)
(*                                   ∨ pred_at auxtr' M0 (λ (_ : LiveState Tid M) ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)). *)
(*         { eapply (IH _ _ _ p _ extr'); eauto. *)
(*           Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)). lia. } *)
(*         exists (1+P). rewrite !pred_at_sum. simpl. done. *)
(*       - exists 1. left. rewrite /pred_at /=. rewrite /role_enabled. *)
(*         destruct auxtr' =>/=. *)
(*         + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver. *)
(*         + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver. *)
(*     Qed. *)

(*   Lemma fairness_preserved_ind ρ: *)
(*     ∀ fm f m ζ (extr: extrace Λ) (auxtr: auxtrace (LM := LM)) δ c, *)
(*       fairness_induction_stmt ρ fm f m ζ extr auxtr δ c. *)
(*   Proof. *)
(*     induction fm as [fm IH] using lex_ind. *)
(*     intros f m ζ extr auxtr δ c Hexinfin Hfair -> Htm -> -> Hfuel Hmapping Hexen. *)
(*     destruct extr as [|c ζ' extr'] eqn:Heq. *)
(*     { have [??] := Hexinfin 1. done. } *)
(*     have Hfair': (forall ζ, fair_ex ζ extr'). *)
(*     { intros. by eapply fair_ex_cons. } *)
(*     destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm. *)
(*     destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first. *)
(*     { exists 0. left. unfold pred_at. simpl. intros contra. eauto. } *)
(*     destruct (decide (Some ζ = ζ')) as [Hζ|Hζ]. *)
(*     - rewrite <- Hζ in *. *)
(*       destruct (traces_match_labels _ _ _ _ _ _ Htm) as [[ρ' ->]| ->]; last first. *)
(*       + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*         unfold ls_trans in Hls. *)
(*         destruct Hls as (? & Hlsdec & Hlsincr). *)
(*         unfold fuel_decr in Hlsdec. *)
(*         have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some ζ). *)
(*         { constructor; eauto. } *)
(*         eapply case1 =>//. *)
(*         * move=> Hinfuel; apply Hlsdec => //; first set_solver. *)
(*         * eapply infinite_cons =>//. *)
(*       + (* Three cases: *) *)
(* (*            (1) ρ' = ρ and we are done *) *)
(* (*            (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases *) *)
(* (*            (3) ρ' ≠ ρ and they don't have the same tid -> *) *)
(* (*            impossible because tid and the label must match! *) *)
(*         inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*         destruct (decide (ρ = ρ')) as [->|Hρneq]. *)
(*         { exists 0. right. rewrite /pred_at /=. eauto. } *)
(*         destruct Hls as (?&Hsame&Hdec&Hnotinc&_). *)
(*         rewrite -Hsame /= in Hmapping. *)
(*         have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some ζ). *)
(*         { constructor; eauto; congruence. } *)
(*         (* Copy and paste begins here *) *)
(*         eapply case1 =>//; last by eauto using infinite_cons. *)
(*         intros Hinfuels. apply Hdec =>//. SS. *)
(*     - (* Another thread is taking a step. *) *)
(*       destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first. *)
(*       { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. } *)
(*       have [ζ'' Hζ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto. *)
(*       destruct (decide (ζ = ζ'')) as [<-|Hchange]. *)
(*       + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f. *)
(*         { destruct ζ' as [ζ'|]; last first; simpl in *. *)
(*           - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*             simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]]. *)
(*             have HnotNone: Some ρ ≠ None by congruence. *)
(*             (* specialize (Hnoninc ρ ltac:(SS) HnotNone). *) *)
(*             specialize (Hnoninc ρ ltac:(SS)). *)
(*             unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc. *)
(*             destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver]. *)
(*             eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//. *)
(*             apply elem_of_dom_2 in Heq. set_solver. *)
(*           - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*             simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done. *)
(*             + destruct Hls as (?&?&?&Hnoninc&?). *)
(*               unfold fuel_must_not_incr in Hnoninc. *)
(*               have Hneq: Some ρ ≠ Some ρ0 by congruence. *)
(*               (* specialize (Hnoninc ρ ltac:(SS) Hneq). *) *)
(*               specialize (Hnoninc ρ ltac:(SS)). *)
(*               unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc. *)
(*               destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver]. *)
(*               eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//. *)
(*               apply elem_of_dom_2 in Heq. set_solver. *)
(*             + destruct Hls as (?&?&Hnoninc&?). *)
(*               unfold fuel_must_not_incr in Hnoninc. *)
(*               have Hneq: Some ρ ≠ None by congruence. *)
(*               (* specialize (Hnoninc ρ ltac:(SS) Hneq). *) *)
(*               specialize (Hnoninc ρ ltac:(SS)). *)
(*               unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc. *)
(*               destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver]. *)
(*               eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//. *)
(*               apply elem_of_dom_2 in Heq. set_solver. } *)

(*         unfold fair_ex in *. *)
(*         have Hζ'en: pred_at extr' 0 (λ (c : cfg Λ) _, locale_enabled ζ c). *)
(*         { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. } *)
(*         destruct m as [| m']. *)
(*         { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen]. *)
(*           - exfalso. apply Hexen. unfold locale_enabled. by eapply (match_locale_enabled _ _ _ _ Htm). *)
(*           - simplify_eq. } *)

(*         have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0) *)
(*                         ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)). *)
(*         { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm. *)
(*           Unshelve. unfold strict, lt_lex. lia. } *)
(*         exists (1+P). rewrite !pred_at_sum. simpl. done. *)
(*       + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f. *)
(*         { destruct ζ' as [ζ'|]; last first; simpl in *. *)
(*           - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*             simpl in *. destruct ℓ; try done. destruct Hls as [_ [Hdec _]]. *)
(*             unfold fuel_decr in Hdec. *)
(*             have Hmd: must_decrease ρ None δ (trfirst auxtr') None. *)
(*             { econstructor. congruence. rewrite Hζ''. eauto. } *)
(*             specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd). *)
(*             unfold oleq in Hdec. rewrite Hfuel in Hdec. *)
(*             destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. *)
(*           - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. *)
(*             simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done. *)
(*             + destruct Hls as (?&?&Hdec&?&?). *)
(*               unfold fuel_decr in Hdec. simplify_eq. *)
(*               have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0). *)
(*               { econstructor 2. congruence. rewrite Hζ''; eauto. } *)
(*               specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd). *)
(*               unfold oleq in Hdec. rewrite Hfuel in Hdec. *)
(*               destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. *)
(*             + destruct Hls as (?&Hdec&_). *)
(*               unfold fuel_decr in Hdec. simplify_eq. *)
(*               have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0). *)
(*               { econstructor 2. congruence. rewrite Hζ''; eauto. } *)
(*               specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd). *)
(*               unfold oleq in Hdec. rewrite Hfuel in Hdec. *)
(*               destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. } *)

(*         unfold fair_ex in *. *)
(*         have: pred_at extr' 0 (λ c _, locale_enabled ζ'' c). *)
(*         { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. } *)
(*         have Hζ'en: pred_at extr' 0 (λ c _, locale_enabled ζ'' c). *)
(*         { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. } *)
(*         have [p Hp] := (Hfair' ζ'' 0 Hζ'en). *)
(*         have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0) *)
(*                         ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)). *)
(*         { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm. *)
(*           Unshelve. unfold strict, lt_lex. lia. } *)
(*         exists (1+P). rewrite !pred_at_sum. simpl. done. *)
(*   Qed. *)

(*   Theorem fairness_preserved (extr: extrace Λ) (auxtr: auxtrace (LM := LM)): *)
(*     infinite_trace extr -> *)
(*     exaux_traces_match extr auxtr -> *)
(*     (forall ζ, fair_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr). *)
(*   Proof. *)
(*     intros Hinfin Hmatch Hex ρ n Hn. *)
(*     unfold pred_at in Hn. *)
(*     destruct (after n auxtr) as [tr|] eqn:Heq =>//. *)
(*     setoid_rewrite pred_at_sum. rewrite Heq. *)
(*     have Hen: role_enabled ρ (trfirst tr) by destruct tr. *)
(*     have [ζ Hζ] : is_Some((trfirst tr).(ls_mapping) !! ρ) by eauto. *)
(*     have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ) by eauto. *)
(*     have Hex' := Hex ζ n. *)
(*     have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ exaux_traces_match tr1' tr *)
(*      by eapply traces_match_after. *)
(*     have Hte: locale_enabled ζ (trfirst tr1'). *)
(*     { rewrite /locale_enabled. have [HiS Hneqζ] := traces_match_first _ _ _ _ _ _ Htr. *)
(*       have [e Hein] := (HiS _ _ Hζ). exists e. split; first done. *)
(*       destruct (to_val e) eqn:Heqe =>//. *)
(*       exfalso. specialize (Hneqζ ζ e Hein). rewrite Heqe in Hneqζ. *)
(*       have HnotNull: Some v ≠ None by []. specialize (Hneqζ HnotNull ρ). done. } *)
(*     setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'. *)
(*     have Hpa: pred_at extr n (λ c _, locale_enabled ζ c). *)
(*     { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. } *)
(*     destruct (Hex' Hpa) as [m Hm]. *)
(*     have ?: infinite_trace tr1'. *)
(*     { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. } *)
(*     eapply (fairness_preserved_ind ρ _ f m ζ _ tr); eauto. *)
(*     intros ?. by eapply fair_ex_after. *)
(*   Qed. *)

(*   Tactic Notation "inv" open_constr(P) := match goal with *)
(*                 | [H: P |- _] => inversion H; clear H; simplify_eq *)
(*                                           end. *)

(* End fairness_preserved. *)

Section fuel_dec_unless.
  Context `{LM: LiveModel (locale Λ) Mdl}.
  Context `{Countable (locale Λ)}.

  Definition Ul (ℓ: LM.(mlabel)) :=
    match ℓ with
    | Take_step ρ _ => Some (Some ρ)
    | _ => None
    end.

  Definition Ψ (δ: LiveState (locale Λ) Mdl) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (G := locale Λ)), f.

  Lemma fuel_dec_unless (auxtr: auxtrace (LM := LM)) :
    auxtrace_valid auxtr ->
    dec_unless ls_under Ul Ψ auxtr.
  Proof.
    intros Hval n. revert auxtr Hval. induction n; intros auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq;
      simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      inversion Hval as [|???? Hmatch]; simplify_eq =>//.
      specialize (IHn _ Hmatch). rewrite Heq // in IHn. }
    edestruct (after 0 auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
    simpl in Heq; simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.

    inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//.
    destruct ℓ as [| tid' |];
      [left; eexists; done| right | inversion Htrans; naive_solver ].
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq). rewrite -> Heq in *. split; last done.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel (trfirst _)) ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }

      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom δ.(ls_fuel))) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      (* destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      (* destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(set_solver)); [done|set_solver].
  Qed.
End fuel_dec_unless.

Section destuttering_auxtr.
  Context `{LM: LiveModel (locale Λ) M}.

  Context `{Countable (locale Λ)}.

  (* Why is [LM] needed here? *)
  Definition upto_stutter_auxtr :=
    upto_stutter (ls_under (G:=locale Λ) (M:=M)) (Ul (LM := LM)).

  Lemma can_destutter_auxtr auxtr:
    auxtrace_valid auxtr →
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{Countable (locale Λ)}.

  Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind (ls_under (G:=locale Λ) (M:=M)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_preserves_validity (auxtr : auxtrace (LM := LM)) mtr:
    upto_stutter_auxtr auxtr mtr ->
    auxtrace_valid auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst. unfold ls_trans in *.
        destruct ℓ; try done. simpl in *. simplify_eq.
        destruct Htrans as [??].
        have <- //: ls_under $ trfirst btr = trfirst str.
        { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
      + right. eapply CH.
        { destruct IH =>//. }
        subst. by inversion Hval.
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{Countable (locale Λ)}.

  Notation upto_stutter_aux := (upto_stutter (ls_under (G := locale Λ)) (Ul (Λ := Λ) (LM := LM))).

  Lemma upto_stutter_mono'' : (* TODO fix this proliferation *)
    monotone2 (upto_stutter_ind (ls_under (G:=locale Λ) (M:=M)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (* role_enabled_model ρ (trfirst mtr) -> *)
    (∃ n, pred_at auxtr n (λ δ _, ¬role_enabled (Λ := Λ) ρ δ)
          ∨ pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ).
    Proof.
      intros Hupto (* Hre *) [n Hstep].
      revert auxtr mtr Hupto (* Hre *) Hstep.
      induction n as [|n]; intros auxtr mtr Hupto (* Hre *) Hstep.
      - punfold Hupto. inversion Hupto; simplify_eq.
        + destruct Hstep as [Hpa|[??]]; try done.
          exists 0. left. rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at /=. destruct mtr; simpl in *; try congruence.
          * exfalso. injection Hstep => Heq. rewrite -> Heq in *.
            unfold Ul in *. congruence.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at //=.
          * rewrite /pred_at //=. injection Hstep. intros Heq. simplify_eq.
            unfold Ul in *. congruence.
      - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
        + destruct Hstep as [?|?]; done.
        + rewrite -> !pred_at_S in Hstep.
          eapply IHn; eauto.
          by pfold.
        + destruct (decide (ℓ' = Some ρ)).
          * simplify_eq.
            exists 0. right. rewrite pred_at_0 //.
          * have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
            { intros P [x ?]. by exists (S x). }
            apply Hw. setoid_rewrite pred_at_S.
            eapply IHn; eauto.
            { destruct IH as [|]; done. }
    Qed.

  Lemma upto_stutter_fairness (auxtr:auxtrace (LM := LM)) (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux ρ auxtr) ->
    (∀ ρ, fair_model_trace ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; last done.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_aux_after ρ auxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' mtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.

From iris.proofmode Require Import tactics.
From stdpp Require Import finite.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

Definition decr_loop_prog (l : loc) : val :=
  rec: "go" <> :=
    if: !#l = #0 then #() else #l <- (!#l - #1);; "go" #().

Definition choose_nat_prog (l : loc) : val :=
  λ: <>,
     #l <- (ChooseNat + #1);;
     decr_loop_prog l.

Inductive CN := Start | N (n : nat).

Definition F_CN (cn : CN) : Z :=
  match cn with
  | Start => -1
  | N n => n
  end.

#[global] Instance CN_eqdec: EqDecision CN.
Proof. solve_decision. Qed.

#[global] Instance YN_inhabited: Inhabited CN.
Proof. exact (populate Start). Qed.

Inductive cntrans: CN -> option unit -> CN -> Prop :=
| start_trans n : cntrans Start (Some ()) (N n)
| decr_trans n : cntrans (N $ S n) (Some ()) (N n)
.

Definition cn_live_roles (cn : CN) : gset unit :=
  match cn with
  | Start => {[ () ]}
  | N n => match n with
           | 0 => ∅
           | S n => {[ () ]}
           end
  end.

Lemma live_spec_holds:
     forall s ρ s', cntrans s (Some ρ) s' -> ρ ∈ cn_live_roles s.
Proof. intros [] ρ s'; [set_solver|]. destruct n; [|set_solver]. inversion 1. Qed.

Definition the_cn_fair_model : FairModel.
Proof.
  refine({|
            fmstate := CN;
            fmrole := unit;
            fmtrans := cntrans;
            live_roles := cn_live_roles;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model : LiveModel heap_lang the_cn_fair_model :=
  {| fuel_limit (x: fmstate the_cn_fair_model) := 40 %nat |}.

Class choose_natPreG Σ := ChooseNatPreG {
  choose_nat_G :> inG Σ (excl_authR ZO);
 }.

Class choose_natG Σ := ChooseNatG {
  choose_nat_gname : gname;
  choose_nat_preG :> inG Σ (excl_authR ZO);
 }.

Global Instance subG_choosenatΣ {Σ} :
  subG (GFunctor (excl_authR ZO)) Σ → choose_natPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_cn_fair_model the_model, choose_natG Σ}.

  Let Ns := nroot .@ "choose_nat".

  Definition choose_nat_inv_inner (γ : gname) (l:loc) : iProp Σ :=
    ∃ (cn:CN), frag_model_is cn ∗ l ↦ #(F_CN cn) ∗ own γ (●E (F_CN cn)).

  Definition choose_nat_inv (γ : gname) (l:loc) :=
    inv Ns (choose_nat_inv_inner γ l).

  Lemma decr_loop_spec γ tid l (n:nat) f :
    6 ≤ f → f ≤ 40 →
    choose_nat_inv γ l -∗
    {{{ has_fuel tid () f ∗ frag_free_roles_are ∅ ∗
        own γ (◯E (Z.of_nat (S n))) }}}
      decr_loop_prog l #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. Admitted.

  (* Lemma decr_loop_spec γ tid l (n:nat) f : *)
  (*   6 ≤ f → f ≤ 40 → *)
  (*   {{{ has_fuel tid () f ∗ frag_free_roles_are ∅ ∗ *)
  (*       own γ (◯E (Z.of_nat (S n))) }}} *)
  (*     decr_loop_prog l @ tid *)
  (*   {{{ RET #(); tid ↦M ∅ }}}. *)
  (* Proof. *)
  (*   iIntros (Hle1 Hle2 Φ) "(Hf & Hr & Hm) HΦ". *)
  (*   iInduction n as [|n] "IHn". *)
  (*   { wp_lam. wp_pures. wp_lam. wp_pures. *)
  (*     iApply (@wp_lift_pure_step_no_fork_singlerole_take_step *)
  (*             _ the_cn_fair_model _ _ *)
  (*             (N 1) (N 0) tid _ _ (f - 6) (f - 3) _ _ _ _ ())=> /=; *)
  (*       [done|set_solver|lia|constructor|]. *)
  (*     do 3 iModIntro. *)
  (*     rewrite has_fuel_fuels. *)
  (*     replace (f - 1 - 1 - 1 - 1 - 1 - 1) with (f - 6) by lia. *)
  (*     iFrame. *)
  (*     iIntros "Hm Hr Hf". *)
  (*     destruct (decide (() ∈ ∅)); [set_solver|]. *)
  (*     wp_pures. by iApply "HΦ". } *)
  (*   wp_lam. *)
  (*   rewrite fmap_insert fmap_empty. (* Sigh.. *) *)
  (*   wp_pures. *)
  (*   rewrite fmap_insert fmap_empty. (* Sigh.. *) *)
  (*   wp_pures. *)
  (*   rewrite fmap_insert fmap_empty. (* Sigh.. *) *)
  (*   iApply (@wp_lift_pure_step_no_fork_singlerole_take_step *)
  (*             _ the_cn_fair_model _ _ *)
  (*             (N $ S $ S n) (N $ S n) tid _ _ (f - 3) f _ _ _ _ ())=> /=; *)
  (*     [done|done|set_solver|lia|constructor|]. *)
  (*   do 3 iModIntro. *)
  (*   rewrite has_fuel_fuels. *)
  (*   replace (f - 1 - 1 - 1) with (f - 3) by lia. *)
  (*   iFrame.     *)
  (*   iIntros "Hm Hr Hf". *)
  (*   wp_pures. *)
  (*   replace (Z.of_nat (S $ S n) - 1)%Z with (Z.of_nat $ S n) by lia. *)
  (*   destruct (decide (() ∈ {[()]})); [|set_solver]. *)
  (*   rewrite has_fuel_fuels. *)
  (*   by iApply ("IHn" with "Hf Hr Hm"). *)
  (* Qed. *)

  Lemma choose_nat_spec γ l tid f :
    8 ≤ f → f ≤ 40 →
    choose_nat_inv γ l -∗
    {{{ has_fuel tid () f ∗ frag_free_roles_are ∅ ∗
        own γ (◯E (-1)%Z) }}}
      choose_nat_prog l #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. Admitted.

  (*   iIntros (Hle1 Hle2 Φ) "(Hf & Hr & Hm) HΦ". *)
  (*   wp_lam. *)
  (*   wp_bind ChooseNat. *)
  (*   iApply (wp_choose_nat_nostep _ _ _ {[() := (f - 2)]} with "[Hf]"). *)
  (*   { set_solver. } *)
  (*   { rewrite -has_fuel_fuels_S has_fuel_fuels. *)
  (*     replace (S (f - 2)) with (f - 1) by lia. done. } *)
  (*   iIntros "!>" (n) "Hf". *)
  (*   iApply (@wp_lift_pure_step_no_fork_singlerole_take_step *)
  (*             _ the_cn_fair_model _ _ *)
  (*             Start (N $ S n) tid _ _ (f - 2) f _ _ _ _ ())=> /=; *)
  (*     [done|done|set_solver|lia|constructor|]. *)
  (*   do 3 iModIntro. *)
  (*   rewrite has_fuel_fuels. *)
  (*   iFrame. *)
  (*   iIntros "Hm Hr Hf". *)
  (*   destruct (decide (() ∈ {[()]})); [|set_solver]. *)
  (*   wp_pures. *)
  (*   replace (Z.of_nat n + 1)%Z with (Z.of_nat $ S n) by lia. *)
  (*   rewrite -has_fuel_fuels. *)
  (*   iApply (decr_loop_spec with "[$Hm $Hr $Hf]"); [lia|lia|]. *)
  (*   done. *)
  (* Qed. *)

End proof.

(* Theorem choose_nat_terminates *)
(*         (extr : extrace) (Hvex : extrace_valid extr) *)
(*         (Hexfirst : (trfirst extr).1 = [choose_nat_prog #()]): *)
(*   (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
(* Proof. *)

Inductive the_order : CN → CN → Prop :=
  | Start_order cn : the_order cn Start
  | N_order n1 n2 : n1 ≤ n2 → the_order (N n1) (N n2).

Local Instance the_order_po: PartialOrder the_order.
Proof.
  split.
  - split.
    + by intros []; constructor.
    + intros [] [] [] Hc12 Hc23; try constructor.
      * inversion Hc23.
      * inversion Hc12.
      * inversion Hc23.
      * inversion Hc12. inversion Hc23. simplify_eq. lia.
  - intros [] []; inversion 1; simplify_eq; try eauto; try inversion 1.
    simplify_eq. f_equal. lia.
Qed.

Definition the_decreasing_role (s : fmstate the_cn_fair_model) : unit :=
  match s with | _ => () end.

#[local] Program Instance the_model_terminates :
  FairTerminatingModel the_cn_fair_model :=
  {|
    ftm_leq := the_order;
    ftm_decreasing_role := the_decreasing_role;
  |}.
Next Obligation.
  assert (∀ n, Acc (strict the_order) (N n)).
  { intros n.
    induction n as [n IHn] using lt_wf_ind.
    constructor. intros cn [Hcn1 Hcn2].
    inversion Hcn1 as [|n1 n2]; simplify_eq.
    destruct (decide (n = n1)) as [->|Hneq]; [done|].
    apply IHn. lia. }
  constructor. intros [] [Hc1 Hc2]; [|done].
  inversion Hc1; simplify_eq. done.
Qed.
Next Obligation.
  intros cn [ρ' [cn' Htrans]]. simpl in *.
  split.
  - rewrite /the_decreasing_role. simpl. rewrite /cn_live_roles.
    destruct cn; [set_solver|].
    destruct n; [inversion Htrans|set_solver].
  - intros cn'' Htrans'.
    destruct cn.
    + split.
      * constructor.
      * intros Hrel. inversion Hrel; simplify_eq.
        inversion Htrans'.
    + split.
      * destruct cn''.
        -- inversion Htrans'.
        -- inversion Htrans'; simplify_eq.
           constructor. lia.
      * intros Hrel.
        inversion Htrans'; simplify_eq.
        inversion Hrel; simplify_eq.
        lia.
Qed.
Next Obligation. done. Qed.
Next Obligation.
  intros cn1 ρ cn2 Htrans.
  destruct cn1.
  - inversion Htrans; simplify_eq. constructor.
  - inversion Htrans; simplify_eq. constructor. lia.
Qed.

#[local] Instance proof_irrel_trans s x :
  ProofIrrel ((let '(s', ℓ) := x in cntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Definition ξ_cn (l:loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace the_cn_fair_model (option unit)) :=
  ∃ (cn:CN), (trace_last extr).2.(heap) !! l = Some #(F_CN cn) ∧
             (trace_last auxtr) = cn.

#[local] Instance proof_irrel_ξ l oζ c' ex atr ℓ δ' :
  ProofIrrel (sim_rel_with_user the_cn_fair_model the_model
                  (ξ_cn l) (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ')).
Proof. apply make_proof_irrel. Qed.

#[local] Instance eq_decision_the_model :
  EqDecision (live_model_to_model the_cn_fair_model the_model).
Proof. Admitted.

#[local] Instance eq_decision_mlabel :
  EqDecision (mlabel (live_model_to_model the_cn_fair_model the_model)).
Proof. solve_decision. Qed.

Theorem choose_nat_sim l
        (extr : extrace) (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [choose_nat_prog l #()]):
  continued_simulation (sim_rel_with_user the_cn_fair_model the_model (ξ_cn l)) (trace_singleton ([choose_nat_prog l #()], {| heap := <[l:=#-1]>∅; used_proph_id := ∅ |}))
                       (trace_singleton (initial_ls (LM := the_model) Start 0%nat)).
Proof.
  assert (heapGpreS #[GFunctor (excl_authR ZO); heapΣ the_cn_fair_model] the_cn_fair_model the_model) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy).
  { done. }
  { clear.
    intros extr atr c' oζ.
    eapply finite_smaller_card_nat.
    simpl.
    eapply (in_list_finite [(_,_)]).
    intros [δ' ℓ] [Hrel [cn [Hextr Hatr]]].
    admit. }
Admitted.

(* Theorem choose_nat_terminates l *)
(*         (extr : extrace) (Hvex : extrace_valid extr) *)
(*         (Hexfirst : (trfirst extr).1 = [choose_nat_prog l #()]): *)
(*   (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
(* Proof. *)
(*   eapply (simulation_adequacy_terminate_ftm (Mdl := the_cn_fair_model) (heapΣ the_cn_fair_model) NotStuck _ Start ∅) =>//. *)
(*   { eapply valid_state_evolution_finitary_fairness. *)
(*     intros ?. simpl. apply (model_finitary s1). } *)
(*   iIntros (HGS) "!> Hm Hr Hs !>". *)
(*   simpl. *)
(*   replace (∅ ∖ {[()]}) with (∅:gset unit) by set_solver. *)
(*   rewrite -fmap_gset_to_gmap. *)
(*   rewrite /gset_to_gmap. simpl. *)
(*   repeat rewrite fmap_insert. *)
(*   repeat rewrite fmap_empty. *)
(*   rewrite -has_fuel_fuels. *)
(*   iApply (choose_nat_spec with "[$Hm $Hr $Hs]"); [simpl;lia|simpl;lia|]. *)
(*   eauto. *)
(* Qed. *)

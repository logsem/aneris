From stdpp Require Import finite decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode simulation_adequacy_lm.
From trillium.fairness.heap_lang Require Import notation.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

(** The program verify liveness for *)
(** Recursion is "off by one" to allow immediate termination after storing 0 *)
Definition decr_loop_prog (l : loc) : val :=
  rec: "go" <> :=
    let: "x" := !#l in
    if: "x" = #1 then #l <- ("x" - #1)
    else #l <- ("x" - #1);; "go" #().
Definition choose_nat_prog (l : loc) : val :=
  λ: <>,
     #l <- (ChooseNat + #1);;
     decr_loop_prog l #().

(** The model state *)
Inductive CN := Start | N (n : nat).

(** A mapping of model state to "program state" *)
Definition CN_Z (cn : CN) : Z :=
  match cn with
  | Start => -1
  | N n => n
  end.

#[global] Instance CN_eqdec: EqDecision CN.
Proof. solve_decision. Qed.

#[global] Instance CN_inhabited: Inhabited CN.
Proof. exact (populate Start). Qed.

Inductive cntrans : CN → option unit → CN -> Prop :=
| start_trans n : cntrans Start (Some ()) (N n)
| decr_trans n : cntrans (N $ S n) (Some ()) (N n).

(* Free construction of the active labels on each state by [cntrans] *)
Definition cn_live_roles (cn : CN) : gset unit :=
  match cn with N 0 => ∅ | _ => {[ () ]} end.

Lemma cn_live_spec_holds s ρ s' : cntrans s (Some ρ) s' -> ρ ∈ cn_live_roles s.
Proof. destruct s; [set_solver|]. destruct n; [|set_solver]. inversion 1. Qed.

Definition cn_fair_model : FairModel.
Proof.
  refine({|
            fmstate := CN;
            fmrole := unit;
            fmtrans := cntrans;
            live_roles := cn_live_roles;
            fm_live_spec := cn_live_spec_holds;
          |}).
Defined.

(** Show that the model is fairly terminating *)

Inductive cn_order : CN → CN → Prop :=
  | cn_order_Start cn : cn_order cn Start
  | cn_order_N (n1 n2 : nat) : n1 ≤ n2 → cn_order (N n1) (N n2).

Local Instance the_order_po: PartialOrder cn_order.
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

Definition cn_decreasing_role (s : fmstate cn_fair_model) : unit :=
  match s with | _ => () end.

#[local] Program Instance cn_model_terminates :
  FairTerminatingModel cn_fair_model :=
  {|
    ftm_leq := cn_order;
    ftm_decreasing_role := cn_decreasing_role;
  |}.
Next Obligation.
  assert (∀ n, Acc (strict cn_order) (N n)).
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
  intros cn [ρ' [cn' Htrans]].
  split.
  - rewrite /cn_decreasing_role. simpl. rewrite /cn_live_roles.
    destruct cn; [set_solver|].
    destruct n; [inversion Htrans|set_solver].
  - intros cn'' Htrans'.
    destruct cn.
    + split; [constructor|].
      intros Hrel. inversion Hrel; simplify_eq. inversion Htrans'.
    + split.
      * destruct cn''.
        -- inversion Htrans'.
        -- inversion Htrans'; simplify_eq. constructor. lia.
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

Definition cn_model : LiveModel (locale heap_lang) cn_fair_model :=
  {| lm_fl _ := 40%nat |}.

(** Determine additional restriction on relation to obtain finite branching *)
Definition ξ_cn (l:loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace cn_fair_model (option unit)) :=
  ∃ (cn:CN), (trace_last extr).2.(heap) !!! l = #(CN_Z cn) ∧
             (trace_last auxtr) = cn.

(** Verify that the program refines the model *)

(* Set up necessary RA constructions *)
Class choose_natG Σ := ChooseNatG { choose_nat_G :> inG Σ (excl_authR ZO) }.

Definition choose_natΣ : gFunctors :=
  #[
     (* heapΣ cn_fair_model cn_RA; *)
     GFunctor (excl_authR ZO) ].

Global Instance subG_choosenatΣ {Σ} : subG choose_natΣ Σ → choose_natG Σ.
Proof. solve_inG. Qed.

Definition Ns := nroot .@ "choose_nat".

Section proof.
  (* Context `{!heapGS Σ cn_model, choose_natG Σ}. *)
  Context `{EM: ExecutionModel M} `{@heapGS Σ _ EM, choose_natG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ cn_fair_model}.
  (* Context `{PMP: @PartialModelPredicates _ _ LM _ _ _ _ _ cn_model PMPP}. *)
  Context `{!fairnessGS cn_model Σ}.

  (** Determine invariant so we can eventually derive ξ_cn from it *)
  Definition choose_nat_inv_inner (γ : gname) (l:loc) : iProp Σ :=
    ∃ (cn:CN), partial_model_is cn ∗ l ↦ #(CN_Z cn) ∗ own γ (●E (CN_Z cn)).

  Definition choose_nat_inv (γ : gname) (l:loc) :=
    inv Ns (choose_nat_inv_inner γ l).

  (* TODO: decide what to do with notations *)
  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

(* From iris.proofmode Require Export tactics. *)
(* From iris.proofmode Require Import coq_tactics reduction spec_patterns. *)


(*   Let myfun: val := λ: <>, #().  *)

(*   Lemma debug_step tid: *)
(*     {{{ has_fuel tid () 1 ∗ frag_free_roles_are ∅ }}} *)
(*          myfun #() @ tid; ⊤ *)
(*     {{{ RET #(); tid ↦M ∅ }}}. *)
(*   Proof using. *)
(*     iIntros (Φ) "[FUEL ROLE] JJ". *)
(*     wp_lam.  *)
    
(*     Set Ltac Backtrace. *)
(*     (* Info 5 wp_pure .  *) *)
(*     iStartProof.  *)
(*     rewrite ?has_fuel_fuels.  *)
(*     Set Ltac Debug.  *)

(* (* Info 5 *) *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) => *)
(*     let e := eval simpl in e in *)
(*     reshape_expr e ltac:(fun K e' => *)
(*       unify e' (App _ _); *)
(*       eapply (tac_wp_pure _ _ _ _ _ K e'); *)
(*         [ *)
(*         | *)
(*         | tc_solve *)
(*         | trivial *)
(*         | let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in *)
(*           iAssumptionCore || fail "wp_pures: cannot find" fs *)
(*         |tc_solve *)
(*         | pm_reduce; *)
(*           simpl_has_fuels; *)
(*           wp_finish *)
(*         ] ; [ solve_fuel_positive *)
(*             | try apply map_non_empty_singleton; try apply insert_non_empty; try done *)
(*             |]) *)
(*     (* || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex" *) *)
(*   (* | _ => fail "wp_pure: not a 'wp'" *) *)
(*   end. *)


  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := cn_model) (PMPP := PMPP) (eGS := heap_fairnessGS))).

  Close Scope Z_scope. 
  Notation "'sub' d" := (fun n => n - d) (at level 10). 

  Lemma sub_comp `{Countable K} (fs: gmap K nat) (d1 d2: nat):
    (sub d1 ∘ sub d2) <$> fs = sub (d1 + d2) <$> fs.
  Proof.
    apply leibniz_equiv.
    apply map_fmap_proper; [| done].
    intros ??->. apply leibniz_equiv_iff.
    rewrite /compose. lia. 
  Qed.

  Lemma sub_0_id `{Countable K} (fs: gmap K nat):
    fs = sub 0 <$> fs.
  Proof.
    rewrite -{1}(map_fmap_id fs).
    apply leibniz_equiv. apply map_fmap_proper; [| done].
    intros ??->. apply leibniz_equiv_iff.
    simpl. lia.
  Qed.

  Ltac solve_fuels_ge_1 FS := 
    intros ?? [? [<- GE]]%lookup_fmap_Some; apply FS in GE; simpl; lia.
  
  Ltac solve_fuels_S FS := 
    iDestruct (has_fuels_gt_1 with "FUELS") as "F";
    [| rewrite -map_fmap_compose; by iFrame];
    solve_fuels_ge_1 FS. 
  
  Ltac pure_step FS :=
    try rewrite sub_comp;
    iApply wp_lift_pure_step_no_fork; auto;
    [| iSplitR; [done| ]; do 3 iModIntro; iSplitL "FUELS"];
    [| solve_fuels_S FS |];
    [by intros ?%fmap_empty_iff| ];
    iIntros "FUELS"; simpl; rewrite sub_comp. 

  Lemma decr_loop_spec γ tid Einvs l (n:nat) (f:nat) :
    7 ≤ f → f ≤ 38 → (↑Ns ∩ Einvs = ∅) ->
    PMP Einvs -∗
    choose_nat_inv γ l -∗
    {{{ has_fuel tid () f ∗ partial_free_roles_are ∅ ∗
        own γ (◯E (Z.of_nat (S n))) }}}
      decr_loop_prog l #() @ tid ; ⊤
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iIntros (Hle1 Hle2 INVS) "#PMP #IH".
    iIntros "!>" (Φ) "(Hf & Hr & Hm) HΦ".

    iDestruct (has_fuel_fuels with "Hf") as "FUELS".
    assert (fuels_ge ({[() := f]}: gmap (fmrole cn_fair_model) nat) 7) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }
    rewrite (sub_0_id {[ _ := _ ]}). 

    iInduction n as [|n] "IHn".
    {
      (* (* Set Printing All. *) *)
      (* (* wp_lam. *) *)
      (* (* let H := fresh in *) *)
      (* (* assert (H := AsRecV_recv).  *) *)
      (* Set Ltac Backtrace. *)
      (* (* rewrite /decr_loop_prog.  *) *)
      (* Info 3 wp_pure (App _ _).  *)
      (* clear H. *)
      rewrite /decr_loop_prog.
      (* wp_lam.  *)

      pure_step FS.

      (* Load - with invariant *)
      wp_bind (Load _).
      iApply wp_atomic.
      iInv Ns as ">HI" "Hclose".
      iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
      iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
      iModIntro.
      (* wp_load. *)

      iApply (wp_load_nostep with "[$] [Hl FUELS]").
      2: { iSplitL "Hl".
           - iNext. iFrame.
           - solve_fuels_S FS. } 
      { set_solver. }
      iModIntro. iIntros "[Hl FUELS]". 

      iMod ("Hclose" with "[Hs Hl Hcn]") as "_"; [ iExists _; iFrame | ].
      iModIntro.
      rewrite Hvalid. clear cn Hvalid.
      (* Store - with invariant *)

      (* wp_pures. *)
      do 5 pure_step FS. 

      replace (Z.of_nat 1 - 1)%Z with 0%Z by lia.
      wp_bind (Store _ _).
      iApply wp_atomic.
      iInv Ns as ">HI" "Hclose".
      iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
      iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
      iModIntro.
      assert (cn = N 1) as ->.
      { destruct cn; inversion Hvalid. by simplify_eq. }
      (* Update the model state to maintain program correspondence *)
      iApply (wp_store_step_singlerole _ _ (():fmrole cn_fair_model) (f - 7) (f-3)
               (* with "[$] [$Hl $Hs $Hr FUELS]" *)
               with "[$] [$Hl $Hs Hr FUELS]"
             ).
      { set_solver. }
      { simpl. lia. }
      { constructor. }
      { set_solver. }
      { iNext. iApply has_fuel_fuels.
        iApply has_fuels_proper; [reflexivity| | iFrame].
        rewrite map_fmap_singleton. done. }
      iIntros "!> (Hl & Hs & Hr & Hf)".
      iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
      { apply (excl_auth_update _ _ 0%Z). }
      iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
      { iExists (N 0). iFrame. }
      iModIntro.
      (* destruct (decide (() ∈ ∅)); [set_solver|]. *)
      by iApply "HΦ". }

    rewrite /decr_loop_prog. 
    pure_step FS. 

    (* Load - with invariant *)
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".

    (* wp_load. *)
    iApply (wp_load_nostep with "[$] [Hl FUELS]").
    2: { iSplitL "Hl".
         - iNext. iFrame.
         - solve_fuels_S FS. } 
    { set_solver. }
    iIntros "!> [Hl FUELS]". 

    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { iExists _. iFrame. }
    iModIntro.
    rewrite Hvalid. clear cn Hvalid.

    (* wp_pures. *)
    do 3 pure_step FS. 

    case_bool_decide as Heq; [inversion Heq; lia|clear Heq].
    do 2 pure_step FS. 

    replace (Z.of_nat (S (S n))  - 1)%Z with (Z.of_nat (S n)) %Z by lia.
    (* Store - with invariant *)
    wp_bind (Store _ _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    assert (cn = N (S (S n))) as ->.
    { destruct cn; inversion Hvalid. by simplify_eq. }
    (* Update the model state to maintain program correspondence *)
    iApply (wp_store_step_singlerole _ _ (():fmrole cn_fair_model) (f - 7)
                                     (f+2) with "[$] [$Hl $Hs FUELS]").
    { set_solver. }
    { simpl. lia. }
    { constructor. }
    { set_solver. }
    { iApply has_fuel_fuels. iNext. iApply has_fuels_proper; [reflexivity| |iFrame].
      rewrite map_fmap_singleton. done. }
    iIntros "!> (Hl & Hs & FUELS)".
    iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
    { apply (excl_auth_update _ _ (Z.of_nat (S n))%Z). }
    iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { iExists (N (S n)). iFrame. }
    iModIntro.
    simpl. destruct (decide (() ∈ {[()]})); [|set_solver].

    iDestruct (has_fuel_fuels with "FUELS") as "FUELS". 
    rewrite (sub_0_id {[ _ := f + 2 ]}). clear FS.    
    assert (fuels_ge ({[() := f + 2]}: gmap (fmrole cn_fair_model) nat) 2) as FS.
    { red. intros ??[? ?]%lookup_singleton_Some. lia. }
    do 2 pure_step FS. 

    (* replace (f + 2 - 1 - 1)%nat with f by lia. *)
    iApply ("IHn" with "[$] [$] [$]").
    iApply has_fuels_proper; [done| | iFrame].
    rewrite !map_fmap_singleton. f_equiv. apply leibniz_equiv_iff. lia. 
  Qed.

  Lemma choose_nat_spec γ l tid Einvs (f:nat) :
    12 ≤ f → f ≤ 40 → (↑Ns ∩ Einvs = ∅) ->
    PMP Einvs -∗
    choose_nat_inv γ l -∗
    {{{ has_fuel tid () f ∗ partial_free_roles_are ∅ ∗ own γ (◯E (-1)%Z) }}}
      choose_nat_prog l #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iIntros (Hle1 Hle2 INVS) "#PMP #IH".
    iIntros "!>" (Φ) "(Hf & Hr & Hm) HΦ".
    (* wp_lam. *)
    iDestruct (has_fuel_fuels with "Hf") as "FUELS".
    assert (fuels_ge ({[() := f]}: gmap (fmrole cn_fair_model) nat) 12) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }
    rewrite (sub_0_id {[ _ := _ ]}). 

    rewrite /choose_nat_prog. pure_step FS. 

    wp_bind ChooseNat.
    iApply (wp_choose_nat_nostep _ _ _ _ {[() := (f - 2)%nat]} with "[$] [FUELS]").
    { set_solver. }
    { rewrite -has_fuel_fuels_S has_fuel_fuels.
      iApply has_fuels_proper; [done| | by iFrame].
      rewrite map_fmap_singleton. f_equiv. apply leibniz_equiv_iff. lia. }
    iIntros "!>" (n) "FUELS".
    clear FS. 
    assert (fuels_ge ({[() := f - 2]}: gmap (fmrole cn_fair_model) nat) 10) as FS.
    { red. intros ??[? ?]%lookup_singleton_Some. lia. }
    rewrite (sub_0_id {[ _ := _ ]}). 
    pure_step FS. 
    (* Store - with invariant *)
    wp_bind (Store _ _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    assert (cn = Start) as ->.
    { destruct cn; inversion Hvalid; [done|]. lia. }
    (* Update the model state to maintain program correspondence *)
    iApply (wp_store_step_singlerole _ _ (():fmrole cn_fair_model)
                                     (* (f - 3) (f-2) _ _ (N (S n)) *)
             with "[$] [Hl Hs FUELS]").    
    { set_solver. }
    4: { iFrame. rewrite has_fuel_fuels. iNext.
         iApply has_fuels_proper; [reflexivity| | by iFrame].
         rewrite map_fmap_singleton. reflexivity. }
    Unshelve. 6: exact (N (S n)). 5: exact (f - 3). 
    { simpl. lia. }
    { constructor. }
    { set_solver. }
    iIntros "!> (Hl & Hs & FUELS)".
    iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
    { apply (excl_auth_update _ _ (Z.of_nat (S n))%Z). }
    iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia.
      iExists (N (S n)). iFrame. }
    iModIntro.
    simpl. destruct (decide (() ∈ {[()]})); [|set_solver].

    clear FS. 
    assert (fuels_ge ({[() := f - 3]}: gmap (fmrole cn_fair_model) nat) 9) as FS.
    { red. intros ??[? ?]%lookup_singleton_Some. lia. }
    rewrite has_fuel_fuels. rewrite (sub_0_id {[ _ := _ ]}). 
    pure_step FS. pure_step FS. 
    
    (* by iApply (decr_loop_spec with "IH [$Hm $Hr $Hf]"); [lia|lia|]. *)
    iApply (decr_loop_spec with "[$] [$] [-HΦ]").
    4: { iFrame. iApply has_fuel_fuels. 
         iApply has_fuels_proper; [reflexivity| | by iFrame].
         rewrite map_fmap_singleton. reflexivity. }
    1, 2: lia.
    { set_solver. }
    done. 
  Qed.

End proof.

(** Construct inverse mapping of program state to model state,
    to compute finite relation *)
Definition Z_CN (v : val) : CN :=
  match v with
  | LitV (LitInt z) =>
      match z with
      | Z0 => N 0
      | Zpos p => N (Pos.to_nat p)
      | Zneg _ => Start         (* Error case when z < -1 *)
      end
  | _ => Start                  (* Error case *)
  end.

Lemma Z_CN_CN_Z cn : Z_CN #(CN_Z cn) = cn.
Proof. destruct cn; [done|]; destruct n; [done|]=> /=; f_equal; lia. Qed.

(** Derive that program is related to model by
    [sim_rel_with_user cn_model (ξ_cn l) using Trillium adequacy *)
Lemma choose_nat_sim l :
  continued_simulation
    (sim_rel_with_user cn_model (ξ_cn l))
    (trace_singleton ([choose_nat_prog l #()],
                        {| heap := {[l:=#-1]};
                           used_proph_id := ∅ |}))
    (trace_singleton (initial_ls (LM := cn_model) Start 0%nat)).
Proof.
  (* assert (heapGpreS choose_natΣ cn_model) as HPreG. *)
  (* { apply _. } *)
  set (Σ := gFunctors.app (heapΣ (@LM_EM _ cn_model)) choose_natΣ).
  assert (heapGpreS Σ (@LM_EM _ cn_model)) as HPreG.
  { apply _. }
  
  eapply (strong_simulation_adequacy
            Σ _ NotStuck _ _ _ ∅). 
  { clear.
    apply rel_finitary_sim_rel_with_user_ξ.
    intros extr atr c' oζ.
    eapply finite_smaller_card_nat=> /=.
    eapply (in_list_finite [(Z_CN (heap c'.2 !!! l), None);
                            (Z_CN (heap c'.2 !!! l), Some ())]).
    (* TODO: Figure out why this does not unify with typeclass *)
    Unshelve. 2: intros x; apply make_proof_irrel.
    intros [cn o] [cn' [Hextr Hatr]].
    rewrite Hextr Z_CN_CN_Z -Hatr. destruct o; [destruct u|]; set_solver. }
  iIntros (?) "!> [Hσ (Hs & Hr & Hf)]".
  iMod (own_alloc) as (γ) "He"; [apply (excl_auth_valid (-1)%Z)|].
  iDestruct "He" as "[He● He○]".
  iMod (inv_alloc Ns ⊤ (choose_nat_inv_inner γ l) with "[He● Hσ Hs]") as "#IH".
  { iIntros "!>". iExists _. iFrame. by rewrite big_sepM_singleton. }

  (* TODO: get rid of it by not requiring empty FR in the first place.
     Also, remove the same trick from other files *)
  iAssert (|==> frag_free_roles_are ∅)%I as "-#FR".
  { rewrite /frag_free_roles_are. iApply own_unit. }
  iMod "FR" as "FR". 

  iModIntro.
  iSplitL.
  { From trillium.fairness Require Import actual_resources_interface. 
    iApply (choose_nat_spec _ _ _ ∅ 40 with "[] IH [Hr Hf He○ FR]").
    4: { iApply ActualOwnershipPartial. }
    1, 2: lia.
    { set_solver. }
    2: by eauto. 
    intros => /=.
    (* replace (∅ ∖ {[()]}) with (∅:gset unit) by set_solver. *)
    rewrite has_fuel_fuels gset_to_gmap_set_to_map. iFrame. }
  iIntros (ex atr c Hvalid Hex Hatr Hends Hξ Hstuck) "_ Hσ ?".
  iInv Ns as ">H".
  iDestruct "H" as (cn) "(Hf & Hl & H●)".
  iDestruct "Hσ" as (Hvalid') "[Hσ Hs]".
  iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup%lookup_total_correct.

  simpl. iDestruct "Hs" as "[Hs TM]". 
  iDestruct (model_agree' with "Hs Hf") as %Hlast.

  iModIntro. iSplitL; [by iExists _; iFrame|].
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. exists cn.
  split; [done|].
  subst. by destruct atr.
Qed.

Theorem choose_nat_terminates l extr :
  trfirst extr = ([choose_nat_prog l #()],
                    {| heap := {[l:=#-1]};
                      used_proph_id := ∅ |}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hexfirst.
  eapply heap_lang_continued_simulation_fair_termination; eauto.
  rewrite Hexfirst. eapply choose_nat_sim.
Qed.

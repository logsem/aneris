From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fuel_ext. 
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness.examples Require Import lm_fair. 

(* Close Scope Z_scope. *)
Section LibraryDefs.

  (* Definition ρl := tt.  *)

  Definition lib_model_impl: FairModel.
    refine ({|
        fmstate := nat;
        fmrole := unit;
        fmtrans s1 oρ s2 := s1 = 1 /\ s2 = 0;
        live_roles s := if (decide (s = 1)) then {[ tt ]} else ∅;
        (* fuel_limit _ := 25%nat; (* exact value; should relax its usage *) *)
             |}).
    intros. set_solver. 
  Defined. 
    

  Definition lib_model: LiveModel heap_lang lib_model_impl := 
    {| lm_fl _ := 5; |}.  
  
  Definition lib_fun: val.
  Admitted.
  
End LibraryDefs.

Global Opaque lib_model_impl. 

Section LibrarySpec.
  Context `{EM: ExecutionModel M} `{@heapGS Σ _ EM}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ lib_model_impl}.
  (* Context {ifG: fairnessGS lib_model Σ}. *)
  
  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := lib_model) (PMPP := PMPP) (eGS := heap_fairnessGS))).

  Lemma lib_spec tid Einvs:
    PMP Einvs -∗
    {{{ partial_model_is 1 (PartialModelPredicatesPre := PMPP) ∗ 
        has_fuels tid {[ tt:=2 ]} (PMPP := PMPP)  }}}
      lib_fun #() @ tid
    {{{ RET #(); partial_mapping_is {[ tid := ∅ ]} ∗ 
                 partial_free_roles_are {[ tt ]} }}}.
  Proof using. Admitted.

End LibrarySpec.

Section ClientDefs.

  Definition lib_fair := LM_Fair (LM := lib_model). 

  Let lib_st := fmstate lib_fair.
  Let lib_role := fmrole lib_fair.

  Definition client_state: Type := lib_st * nat.

  Inductive y_role := ρy.
  Definition client_role: Type := lib_role + y_role.
  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_y_step_2 lb:
    client_trans (lb, 2) (Some $ inr ρy) (lb, 1)
  (* TODO: allow arbitrary library's LM roles *)
  | ct_lib_step lb1 lb2
                (LIB_STEP: fmtrans lib_fair lb1 (Some 0%nat) lb2):
    client_trans (lb1, 1) (Some $ inl 0%nat) (lb2, 1)
  | ct_y_step_1 (lb: fmstate lib_fair)
                (* (LIB_NOSTEP: 0 ∉ live_roles _ lb) *)
                (LIB_NOROLES: ls_tmap lb (LM := lib_model) !! 0 = Some ∅)
    :
    client_trans (lb, 1) (Some $ inr ρy) (lb, 0)
  .

  Global Instance lib_role_EqDec: EqDecision lib_role.
  Proof. solve_decision. Defined. 
  Global Instance lib_role_Cnt: Countable lib_role.
  Proof using. rewrite /lib_role. simpl. apply _. Defined. 
  

  Global Instance client_role_EqDec: EqDecision client_role.
  Proof. Admitted. 
  Global Instance client_role_Cnt: Countable client_role.
  Proof using. Admitted. 


  Definition client: val :=
  λ: <>,
    let: "x" := ref #2 in
    "x" <- #1 ;;
    lib_fun #() ;;
    "x" <- #0 ;;
    Skip
  .

  Instance lib_step_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof. Admitted. 
  
  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (lib_step_dec st r) = true))  {[ inl 0; inr ρy ]}. 

  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role),
      (exists s', client_trans s (Some ρ) s') <-> ρ ∈ client_lr s.
  Proof.
    intros ??. rewrite /client_lr.
    rewrite elem_of_filter. rewrite @bool_decide_eq_true.
    rewrite elem_of_union. rewrite !elem_of_singleton. 
    split.
    - intros [? TRANS]. split; eauto. inversion TRANS; subst; eauto.
    - tauto. 
  Qed. 

  Definition client_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    intros. eapply client_lr_spec; eauto. 
  Defined.

  Definition client_fl := 10. 
  Definition client_model: LiveModel heap_lang client_model_impl :=
    {| lm_fl _ := client_fl; |}.  

  Class clientPreGS (Σ: gFunctors) := ClientPreGS {
     cl_pre_fuel :> inG Σ (authUR (gmapUR (RoleO lib_model_impl) (exclR natO)));
     cl_pre_lib_st :> inG Σ (authUR (optionR (exclR (ModelO lib_model_impl))));
     cl_pre_y_st :> inG Σ (authUR (optionR (exclR natO)));
     (* TODO: generalize key type *)
     cl_pre_mapping :> inG Σ (authUR (gmapUR (localeO heap_lang) (exclR (gsetR (RoleO lib_model_impl)))));
     cl_pre_fr :> inG Σ (authUR (gset_disjUR (RoleO lib_model_impl)));
  }.

  Class clientGS Σ := ClientGS {
    cl_pre_inG :> clientPreGS Σ;
    cl_y_st_name : gname;
    cl_lib_st_name : gname;
    cl_fuel_name : gname;
    cl_fr_name : gname;
    cl_map_name : gname;
  }.

End ClientDefs. 

Section ClientRA.
  Context `{EM: ExecutionModel M} `{@heapGS Σ _ EM} {cG: clientGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ client_model_impl}.
  
  Notation "'lib_inn_role'" := (fmrole lib_model_impl).
  Notation "'lib_inn_state'" := (fmstate lib_model_impl).
  Notation "'lib_state'" := (fmstate lib_fair).

  Definition lib_auth_fuel_is (F: gmap lib_inn_role nat): iProp Σ :=
    own cl_fuel_name
        (● ((fmap Excl F): ucmra_car (gmapUR (RoleO lib_model_impl) (exclR natO)))).

  Definition lib_frag_fuel_is (F: gmap lib_inn_role nat): iProp Σ :=
    own cl_fuel_name
        (◯ ((fmap Excl F): ucmra_car (gmapUR (RoleO lib_model_impl) (exclR natO)))).

  (* TODO: generalize the type of keys *)
  Definition lib_auth_mapping_impl_is (m: gmap (locale heap_lang) (gset lib_inn_role)): iProp Σ :=
    own cl_map_name
        (● (fmap Excl m : ucmra_car (gmapUR _ (exclR (gsetR lib_inn_role))))).

  Definition lib_frag_mapping_impl_is (m: gmap (locale heap_lang) (gset lib_inn_role)): iProp Σ :=
    own cl_map_name
        (◯ (fmap Excl m : ucmra_car (gmapUR _ (exclR (gsetR lib_inn_role))))).

  Definition lib_auth_model_is (fm: lib_inn_state): iProp Σ :=
    own cl_lib_st_name (● Excl' fm).

  Definition lib_frag_model_is (fm: lib_inn_state): iProp Σ :=
    own cl_lib_st_name (◯ Excl' fm).

  Definition lib_auth_free_roles_are (FR: gset lib_inn_role): iProp Σ :=
    own cl_fr_name (● (GSet FR)).

  Definition lib_frag_free_roles_are (FR: gset lib_inn_role): iProp Σ :=
    own cl_fr_name (◯ (GSet FR)).

  Definition y_auth_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (● Excl' y).

  Definition y_frag_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (◯ Excl' y).

  (* TODO: can it be unified with definition in resources.v ? *)
  Definition lib_msi (δ: lib_state): iProp Σ := 
    lib_auth_fuel_is (ls_fuel δ) ∗ 
    lib_auth_mapping_impl_is (ls_tmap δ (LM := lib_model)) ∗
    lib_auth_model_is δ ∗ 
    ∃ FR, lib_auth_free_roles_are FR ∗
          ⌜ FR ∩ dom (ls_fuel δ) = ∅ ⌝.

  Definition client_inv_impl (st: client_state) : iProp Σ :=
    let (lb, y) := st in
    partial_model_is st ∗
    y_auth_model_is y ∗
    lib_msi lb. 

  Definition Ns := nroot .@ "client".

  Definition client_inv: iProp Σ :=
    inv Ns (∃ (st: client_state), client_inv_impl st).

End ClientRA.


Section ClientSpec. 
  Context `{EM: ExecutionModel M} `{@heapGS Σ _ EM} {cpG: clientPreGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ client_model_impl}.

  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS))).

  Notation "'sub' d" := (fun n => n - d) (at level 10). 

  Lemma sub_comp `{Countable K} (fs: gmap K nat) (d1 d2: nat):
    (sub d1 ∘ sub d2) <$> fs = sub (d1 + d2) <$> fs.
  Proof.
    apply leibniz_equiv. apply map_fmap_proper; [| done].
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

  Ltac solve_map_not_empty := intros ?MM%fmap_empty_iff; try apply map_non_empty_singleton in MM; set_solver. 

  Ltac pure_step FS :=
    try rewrite sub_comp;
    iApply wp_lift_pure_step_no_fork; auto;
    [| iSplitR; [done| ]; do 3 iModIntro; iSplitL "FUELS"];
    [| solve_fuels_S FS |];
    (* [by intros ?%fmap_empty_iff| ]; *)
    [solve_map_not_empty| ];
    iIntros "FUELS"; simpl; rewrite sub_comp. 

  Lemma init_client_inv lb0 n:
    partial_model_is (lb0, n)  ={∅}=∗ 
    ∃ (cG: clientGS Σ), client_inv ∗
                        lib_frag_fuel_is (ls_fuel lb0) ∗
                        lib_frag_mapping_impl_is (ls_tmap lb0 (LM := lib_model)) ∗
                        lib_frag_model_is lb0 ∗
                        lib_frag_free_roles_are ∅ ∗
                        y_frag_model_is n.
  Proof using cpG.
    (* simpl in lb0. red in lb0.   *)
    iIntros "ST".
    iMod (own_alloc ((● (Excl' (ls_under lb0)) ⋅ ◯ _))) as (γ_lib) "[AUTH_LIB FRAG_LIB]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }
    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }
    iMod (own_alloc ((● (Excl <$> ls_tmap lb0 (LM := lib_model)) ⋅ ◯ _ ): (authUR (gmapUR (localeO heap_lang) (exclR (gsetR (RoleO lib_model_impl))))))) as (γ_map) "[AUTH_MAP FRAG_MAP]".
    { apply auth_both_valid_discrete. split; [reflexivity|].
      intros i. rewrite lookup_fmap. by destruct lookup. } 
    iMod (own_alloc (((● (Excl <$> ls_fuel lb0)) ⋅ ◯ _): (authUR (gmapUR (RoleO lib_model_impl) (exclR natO))))) as (γ_fuel) "[AUTH_FUEL FRAG_FUEL]".
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      intros i. rewrite lookup_fmap. by destruct lookup. } 
    iMod (own_alloc ((● (GSet ∅)  ⋅ ◯ _): authUR (gset_disjUR (RoleO lib_model_impl)))) as (γ_fr) "[AUTH_FR FRAG_FR]".
    { apply auth_both_valid_2 =>//. }

    set (cG := {| 
                cl_pre_inG := cpG;
                cl_y_st_name := γ_st;
                cl_lib_st_name := γ_lib;
                cl_fuel_name := γ_fuel;
                cl_fr_name := γ_fr;
                cl_map_name := γ_map 
              |}). 
 
    iMod (inv_alloc Ns _  (∃ st, client_inv_impl st) with "[-FRAG_LIB FRAG_Y FRAG_MAP FRAG_FR FRAG_FUEL]") as "#INV".
    { iNext. rewrite /client_inv_impl /lib_msi.
      iExists (_, _). iFrame.  
      iExists ∅. iFrame. iPureIntro. set_solver. }

    iModIntro. iExists _. iFrame. done. 
  Qed.

  (* TODO: remove tid=0 restriction ? *)
  Let lib_pmi `{clientGS Σ} (m: gmap (locale heap_lang) (gset (fmrole lib_model_impl))): iProp Σ:=
    (∃ (L: gset (fmrole lib_model_impl)) (Ract Rfr: gset client_role), 
        ⌜ m = {[ 0 := L ]} ⌝ ∗
         lib_frag_mapping_impl_is {[ 0 := L ]} ∗
         (⌜ L ≠ ∅ ⌝ ∗ ⌜ Ract = {[ inl 0 ]} /\ Rfr = {[ inr ρy ]} ⌝ ∗ (∃ f: nat, partial_fuel_is {[ inl 0 := f ]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∨
          ⌜ L = ∅ ⌝ ∗ ⌜ Ract = {[ inr ρy ]} /\ Rfr = {[ inl 0 ]} ⌝ ∗ partial_fuel_is {[ inr ρy := 10 ]}) ∗
        partial_mapping_is {[ 0 := Ract ]} ∗
        partial_free_roles_are Rfr ∗
        y_frag_model_is 1). 
  
  Definition lib_PMPP `{clientGS Σ}:
    @PartialModelPredicatesPre heap_lang _ _ Σ lib_model_impl.
   refine
    {|
        partial_model_is := lib_frag_model_is;
        partial_free_roles_are := lib_frag_free_roles_are;
        partial_fuel_is := lib_frag_fuel_is;
        partial_mapping_is := lib_pmi;
    |}.
  Unshelve.
  all: try apply _. 
  - intros ???. set_solver.
  - intros ???. iSplit. 
    all: by iIntros "(%&%&%& (-> & ?))"; do 3 iExists _; iFrame; iPureIntro; apply leibniz_equiv.
  - intros. rewrite /lib_frag_fuel_is.
      rewrite map_fmap_union. rewrite -gmap_disj_op_union.
      2: { by apply map_disjoint_fmap. }
      by rewrite auth_frag_op own_op.
  - intros. rewrite /lib_frag_free_roles_are.
      rewrite -gset_disj_union; auto.  
      by rewrite auth_frag_op own_op.
  - iApply own_unit.
  Defined.

  (* statement copied from actual_resources
     TODO: is it possible to reuse its proof? *)
  Lemma lib_update_no_step_enough_fuel `{clientGS Σ}
  (δ1: lib_model) rem
  (* c1 c2 *)
  fs ζ:
    (dom fs ≠ ∅) ->
    (live_roles lib_model_impl δ1) ∩ rem = ∅ →
    rem ⊆ dom fs →
    (* locale_step c1 (Some ζ) c2 -> *)
    has_fuels_S ζ fs (PMPP := lib_PMPP) -∗ lib_msi δ1
    ==∗ ∃ δ2,
        ⌜ lm_ls_trans lib_model δ1 (Silent_step ζ) δ2 ⌝ ∗
        has_fuels ζ (fs ⇂ (dom fs ∖ rem)) (PMPP := lib_PMPP) ∗
        lib_msi δ2 ∗
        ⌜ ls_tmap δ2 (LM := lib_model) = <[ζ:=dom (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs)]> (ls_tmap δ1 (LM := lib_model)) ⌝. 
  Proof. Admitted. 

  Lemma live_roles_1 lb:
    live_roles client_model_impl (lb, 1) = 
    if (decide (0 ∈ live_roles _ lb)) 
    then {[ inl 0 ]} 
    else if decide (ls_tmap lb (LM := lib_model) !! 0 = Some ∅) 
         then {[ inr ρy ]} 
         else ∅. 
  Proof. 
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite filter_union.

    destruct (decide (0 ∈ live_roles lib_fair lb)) as [LR | LR].
    - pose proof (LM_live_role_map_notempty _ _ LR) as (?&MAP&?).
      erewrite filter_singleton, filter_singleton_not, decide_True.
      + set_solver.
      + eauto.
      + rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst. set_solver.
      + rewrite bool_decide_eq_true_2; [done| ].
        eapply LM_live_roles_strong in LR as [? ?]. eauto. 
        eexists. eapply ct_lib_step. simpl. eauto.
    - rewrite filter_singleton_not; [rewrite decide_False| ]. 
      2: { intros [DOM LIVE]%elem_of_filter.
           by apply LM_live_roles_strong in DOM. }
      2: { rewrite bool_decide_eq_false_2; [done| ].
           intros [? STEP]. inversion STEP. subst. simpl in LIB_STEP.
           destruct LR. apply LM_live_roles_strong. eauto. }
      destruct (ls_tmap lb (LM := lib_model) !! 0) eqn:MAP0; rewrite MAP0.
      + destruct (decide (g = ∅)) as [-> | ?]. 
        * erewrite decide_True; [| done].
          rewrite filter_singleton; [set_solver| ].
          rewrite bool_decide_eq_true_2; [done| ]. eexists. by econstructor.
        * erewrite decide_False.
          2: { intros [=]. done. }
          rewrite filter_singleton_not; [set_solver| ].
          rewrite bool_decide_eq_false_2; [done| ].
          intros [? STEP]. inversion STEP. subst.
          rewrite MAP0 in LIB_NOROLES. congruence.
      + erewrite decide_False; [| done].
        rewrite filter_singleton_not; [set_solver| ].
        rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst.
        rewrite MAP0 in LIB_NOROLES. congruence.
  Qed. 

  Lemma live_roles_2 lb0:
    live_roles client_model_impl (lb0, 2) ≡ {[ inr ρy ]}.
  Proof. 
    simpl. rewrite /client_lr.
    rewrite filter_union.
    erewrite filter_singleton_not, filter_singleton; [set_solver| ..].
    - rewrite bool_decide_eq_true_2; [done| ]. eexists. econstructor.
    - apply not_true_iff_false. 
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
  Qed. 

  (* Lemma live_roles_1' lb0 R *)
  (*   (LB0_R: ls_tmap lb0 !! 0 = Some R) *)
  (*   : *)
  (*   live_roles client_model_impl (lb0, 1) = if decide (R = ∅) then ∅ else {[ inl 0 ]}. *)
  (* Proof.  *)
  (*   simpl. rewrite /client_lr. *)
  (*   (* pose proof LB0_ACT as LB0_ACT_. *) *)
  (*   apply leibniz_equiv. rewrite filter_union. *)
  (*   (* simpl in LB0_ACT. *) *)
  (*   (* apply elem_of_filter in LB0_ACT as [[? STEP'] IN]. *) *)
  (*   (* red in STEP'.  *) *)
  (*   rewrite union_comm.  *)
  (*   erewrite filter_singleton_not. *)
  (*   2:  *)
    
  (*   - apply not_true_iff_false.  *)
  (*     rewrite bool_decide_eq_false_2; [tauto| ]. *)
  (*     intros [? STEP]. inversion STEP. subst. *)
  (*     apply LM_live_role_map_notempty in LB0_ACT_ as [? [??]]. set_solver. *)
  (*   - rewrite bool_decide_eq_true_2; [done| ]. *)
  (*     eexists. apply ct_lib_step. simpl. eauto. *)
  (* Qed.   *)

  (* Lemma live_roles_1'' lb *)
  (*   (* (NOACT: ls_tmap lb !! 0 = Some ∅) *) *)
  (*   (NOACT: 0 ∉ live_roles _ lb) *)
  (*   : *)
  (*   live_roles client_model_impl (lb, 1) = {[ inr ρy ]}. *)
  (* Proof.  *)
  (*   simpl. rewrite /client_lr. *)
  (*   apply leibniz_equiv. rewrite filter_union. *)
  (*   erewrite filter_singleton_not, filter_singleton; [set_solver| ..]. *)
  (*   - rewrite bool_decide_eq_true_2; [done| ]. *)
  (*     eexists. by eapply ct_y_step_1. *)
  (*   - rewrite bool_decide_eq_false_2; [done| ]. *)
  (*     intros [? STEP]. *)
  (*     apply NOACT. apply LM_live_roles_strong. *)
  (*     inversion STEP; subst. *)
  (*     eexists. simpl in LIB_STEP. eauto.  *)
  (* Qed.  *)

  (* Lemma live_roles_1 lb: *)
  (*   live_roles client_model_impl (lb, 1) =  *)
  (*   {[ if (decide (0 ∈ live_roles _ lb)) then inl 0 else inr ρy ]}. *)
  (* Proof.  *)
  (*   destruct decide; auto using live_roles_1', live_roles_1''. *)
  (* Qed. *)

  Tactic Notation "specialize_full" ident(H) :=
    let foo := fresh in
    evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].

  Lemma update_client_state `{clientGS Σ} Einvs
    (extr: execution_trace heap_lang) (mtr: auxiliary_trace M)
    c2 (lb lb': fmstate lib_fair) f
    (LIB_STEP: locale_trans lb 0 lb' (LM := lib_model))
    (PROG_STEP: locale_step (trace_last extr) (Some 0) c2)
    (F_BOUND: f ≤ client_fl)
    :
    PMP Einvs ⊢
    em_msi (trace_last extr) (trace_last mtr) (em_GS0 := heap_fairnessGS) -∗ 
    partial_model_is (lb, 1) -∗
    partial_free_roles_are {[inr ρy]} -∗
    has_fuels 0 {[inl 0 := f]}
    ={Einvs}=∗
    ∃ (δ2 : M) (ℓ: mlabel M),
      ⌜em_valid_evolution_step (Some 0) c2 (trace_last mtr) ℓ δ2⌝ ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS) ∗
      has_fuels 0 (if decide (ls_tmap lb' (LM := lib_model) !! 0 = Some ∅)
                   then {[inr ρy := client_fl]}
                   else {[inl 0 := f]}) ∗
      partial_model_is (lb', 1) ∗
      partial_free_roles_are
      (if decide (ls_tmap lb' (LM := lib_model) !! 0 = Some ∅) then {[inl 0]} else {[inr ρy]}).
  Proof.
    
    iIntros "#PMP MSI ST FR FUELS".
    Local Ltac dEq := destruct (decide (_ = _)). 
    Local Ltac dEl := destruct (decide (_ ∈ _)). 
    pose proof (LM_map_empty_notlive lb' 0 (LM := lib_model)).

    pose proof (live_roles_1 lb) as LIVE. rewrite decide_True in LIVE. 
    2: { eapply LM_live_roles_strong. eexists. eauto. }
    (* TODO: consider the case with rem ≠ ∅ *)
    pose proof (live_roles_1 lb') as LIVE'.

    remember (trace_last extr) as c1. destruct c1 as (σ1, tp1).
    destruct c2 as (σ2, tp2).

    iPoseProof (update_step_still_alive with "[$] [$] [$] [$] [$]") as "EM_STEP".
    7: { apply PROG_STEP. }
    7: { apply ct_lib_step. simpl. eauto. }
    { rewrite LIVE LIVE'. dEl; set_solver. }
    { rewrite dom_singleton. 
      assert ((if (decide (ls_tmap lb' (LM := lib_model) !! 0 = Some ∅))
              then {[ inl 0 ]}
              else (∅: gset (fmrole client_model_impl))) ⊆ {[inl 0]}) as IN.
      { dEq; set_solver. }
      apply IN. }
    { rewrite LIVE. set_solver. }
    all: eauto.
    { Unshelve. 
      2: exact (if decide (ls_tmap lb' (LM := lib_model) !! 0 = Some ∅) 
                then {[ inr ρy := client_fl ]} 
                else {[ inl 0 := f ]}).
      destruct (decide (_=_)); set_solver. }
    { repeat split; rewrite ?LIVE ?LIVE'.
      - dEl.
        2: { destruct decide; set_solver. }
        intros _. rewrite decide_False. 
        { rewrite lookup_singleton. simpl. lia. }
        tauto. 
      - destruct (decide (_ ∈ _)); [set_solver| ].
        destruct (decide (_=_)); [set_solver| ].
        rewrite !lookup_singleton. simpl. lia. 
      - set_solver.
      - dEq; [| set_solver]. 
        intros. assert (ρ' = inr ρy) as -> by set_solver.
        rewrite lookup_singleton. simpl. lia.
      - dEq; set_solver.
      - dEq; dEl; set_solver.
      - dEq; dEl; set_solver. }
    rewrite LIVE LIVE'.
    iMod "EM_STEP" as (??) "(?&?&?&?&FREE)".
    iModIntro. do 2 iExists _. iFrame.
    
    iApply partial_free_roles_are_Proper; [| iFrame].
    dEl; dEq; tauto || set_solver.  
  Qed.
 

  Lemma fuel_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  PMP Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M) 
    (c2 : cfg heap_lang) (fs : gmap (fmrole lib_model_impl) nat) 
    (ζ : locale heap_lang) (_ : dom fs ≠ ∅) (_ : locale_step 
                                                   (trace_last extr) 
                                                   (Some ζ) c2),
    has_fuels ζ (S <$> fs) (PMPP := lib_PMPP) -∗
    em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS)
    ={Einvs ∪ ↑Ns}=∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
         (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) (PMPP := lib_PMPP) ∗ 
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB MSI". simpl in *.
    
    iInv Ns as ((lb, y)) ">(ST & YST_AUTH & inv')" "CLOS".    

    iAssert (⌜ ζ = 0 /\ y = 1 /\ 
               ls_tmap lb !! 0 = Some (dom (S <$> fs)) /\
               S <$> fs ⊆ ls_fuel lb ⌝)%I as %(->&->&TMAP0&FUEL0).
    { iDestruct "FUELS_LIB" as "[MAP_LIB FUEL_LIB]".
      simpl. iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)". 
      assert (ζ = 0 /\ L = dom (S <$> fs)) as [-> ->] by set_solver. clear LIBM.
      iDestruct "MATCH" as "[(_&[-> ->]&X) | [% _]]".
      2: { exfalso. set_solver. }
      iAssert (⌜ y = 1 ⌝)%I as %->.
      { (* exploit auth and frag parts of y state*)
      admit. }
      (* iAssert (⌜  ⌝)%I as %MAPlb. *)
      (* { admit. }  *)
      (* iAssert (⌜ ⌝)%I as %FUELlb. *)
      (* { admit. } *)
      admit. }
    
    iMod (lib_update_no_step_enough_fuel with "FUELS_LIB inv'") as (lb')  "(%LIB_STEP & FUELS_LIB & MSI_LIB & %TMAP_LIB)".
    3: { apply empty_subseteq. }
    { eauto. }
    { set_solver. }
    
    destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2).
    rewrite LASTE. 
    rewrite difference_empty_L. rewrite difference_empty_L in TMAP_LIB.
    iDestruct "FUELS_LIB" as "[MAP_LIB FUEL_LIB]".
    rewrite dom_domain_restrict; [| set_solver].
    simpl.  iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    iDestruct "MATCH" as "[(_&[-> ->]&[%f [FUEL0 %BOUND0]]) | [% _]]".
    2: { exfalso. set_solver. }    
    iAssert (has_fuels 0 {[ inl 0 := f ]}) with "[MAP FUEL0]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -LASTE. 
    iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto.
    { econstructor. eauto. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".

    iMod ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "_".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }

    iModIntro.
    iDestruct "FUELS" as "[MAP FUEL]". 
    rewrite /has_fuels. iSplitR "FUEL_LIB".
    2: { rewrite dom_domain_restrict; [| set_solver]. done. }
    simpl. rewrite dom_domain_restrict; [| set_solver].
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done| ].
    assert (L = dom fs) as ->; [set_solver| ].
    (* TODO: case when domain becomes empty *)
    iLeft. iSplitR; [done| ].
    rewrite dom_domain_restrict in TMAP_LIB; [| set_solver].
    rewrite TMAP_LIB. rewrite lookup_insert.
    repeat erewrite @decide_False with (P := (Some (dom fs) = Some ∅)).
    2-3: by intros [=].
    iSplitR.
    - iPureIntro. set_solver.
    - rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. 
      iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst.  
      iExists _. iFrame. iPureIntro. lia.
    Admitted.
  
  (* copied from actual_resources
     TODO: try to reuse its proof *)
  Lemma lib_update_step_still_alive `{clientGS Σ}
        s1 s2 fs1 fs2 ρ (δ1 : lib_model) ζ fr1 fr_stash:
    (live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ->
    fr_stash ⊆ dom fs1 ->
    (live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅ ->
    dom fs2 ∩ fr_stash = ∅ ->    
    fmtrans _ s1 (Some ρ) s2 -> 
    valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := lib_model) ->
    has_fuels ζ fs1 (PMPP := lib_PMPP) -∗ 
    partial_model_is s1 (PartialModelPredicatesPre := lib_PMPP) -∗ 
    lib_msi δ1 -∗
    partial_free_roles_are fr1 (PartialModelPredicatesPre := lib_PMPP)
    ==∗ ∃ (δ2: lib_model),
        ⌜lm_ls_trans lib_model δ1 (Take_step ρ ζ) δ2 ⌝ ∗
        has_fuels ζ fs2 (PMPP := lib_PMPP) ∗ 
        partial_model_is s2 (PartialModelPredicatesPre := lib_PMPP) ∗ 
        lib_msi δ2 ∗
        partial_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash) (PartialModelPredicatesPre := lib_PMPP) ∗
        ⌜ ls_tmap δ2 (LM := lib_model) = (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := lib_model))) ⌝.
  Proof. Admitted. 

  Lemma model_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  PMP Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M)
    (tp1 tp2 : list (language.expr heap_lang)) (σ1 σ2 : language.state heap_lang)
    (s1 s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat)
    (ρ : fmrole lib_model_impl) (δ1 : M) (ζ : locale heap_lang)
    (fr1 fr_stash : gset (fmrole lib_model_impl))
    (_ : live_roles lib_model_impl s2 ∖ live_roles lib_model_impl s1 ⊆ fr1)
    (_ : fr_stash ⊆ dom fs1) (_ : live_roles lib_model_impl s1
                                  ∩ (fr_stash ∖ {[ρ]}) = ∅)
    (_ : dom fs2 ∩ fr_stash = ∅) (_ : trace_last extr = (tp1, σ1))
    (_ : trace_last auxtr = δ1) (_ : locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
    (_ : fmtrans lib_model_impl s1 (Some ρ) s2)
    (_ : valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := lib_model))
  ,
    has_fuels ζ fs1 (PMPP := lib_PMPP) -∗
    partial_model_is s1 (PartialModelPredicatesPre := lib_PMPP) -∗
    em_msi (tp1, σ1) δ1 (em_GS0 := heap_fairnessGS) -∗
    partial_free_roles_are fr1 (PartialModelPredicatesPre := lib_PMPP)
    ={Einvs ∪ ↑Ns}=∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: (tp2, σ2))
         (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ fs2 (PMPP := lib_PMPP) ∗
      partial_model_is s2 (PartialModelPredicatesPre := lib_PMPP) ∗
      em_msi (tp2, σ2) δ2 (em_GS0 := heap_fairnessGS) ∗
      partial_free_roles_are
        (fr1 ∖ (live_roles lib_model_impl s2 ∖ live_roles lib_model_impl s1)
         ∪ fr_stash) (PartialModelPredicatesPre := lib_PMPP).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI FR_LIB". simpl in *.
    
    assert (ρ ∈ dom fs1) as DOM1ρ by apply x7.     
    
    iInv Ns as ((lb, y)) ">(ST & YST_AUTH & inv')" "CLOS".
    iAssert (⌜ ζ = 0 /\ y = 1 /\ 
               ls_tmap lb !! 0 = Some (dom fs1) /\
               fs1 ⊆ ls_fuel lb ⌝)%I as %(->&->&TMAP&FUEL).
    { iDestruct "FUELS_LIB" as "[MAP_LIB FUEL_LIB]".
      simpl. iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)". 
      assert (ζ = 0 /\ L = dom fs1) as [-> ->] by set_solver. clear LIBM.
      iDestruct "MATCH" as "[(_&[-> ->]&X) | [% _]]".
      2: { set_solver. }
      iAssert (⌜ y = 1 ⌝)%I as %->.
      { (* exploit auth and frag parts of y state*)
      admit. }
      (* iAssert (⌜  ⌝)%I as %MAPlb. *)
      (* { admit. }  *)
      (* iAssert (⌜ ⌝)%I as %FUELlb. *)
      (* { admit. } *)
      admit. }
    
    iPoseProof (lib_update_step_still_alive with "[$] [$] [$] [$]") as "LIFT"; eauto.
    iMod "LIFT" as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & FR_LIB & %TMAP_LIB)".
    simpl. iFrame "ST_LIB". 
    
    iDestruct "FUELS_LIB" as "[MAP_LIB FUEL_LIB]".
    simpl.  iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    (* iDestruct "MATCH" as "[(_&[-> ->]&[%f [FUEL0 %BOUND0]]) | [% _]]". *)
    (* 2: { set_solver. } *)
    assert (L = dom fs2) as -> by set_solver. clear LIBM.
    simpl. 
    iAssert (has_fuels 0 {[ inl 0 := f ]}) with "[MAP FUEL0]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -x3 -x4. 
    iPoseProof (update_client_state with "[$] [] [] [$] [$]") as "EM_STEP"; eauto.
    { econstructor. eauto. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".


    
    


  Lemma lib_PMP `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
    PMP Einvs ∗ client_inv ⊢
    (* PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl1_PMPP γ)).  *)
    PartialModelPredicates (Einvs ∪ ↑Ns) (EM := EM) (iLM := lib_model) (PMPP := lib_PMPP) (eGS := heap_fairnessGS).
  Proof. 
    iIntros "[#PMP #COMP]". iApply @Build_PartialModelPredicates.

    iModIntro. repeat iSplitR.
    - iIntros "* FUELS_LIB MSI".
      iDestruct (fuel_step_lifting with "[$] [] [] FUELS_LIB MSI") as "LIFT"; eauto.
      (* change the PMP interface so it allows fupd in fuel step *)
      admit.
    - (* TODO: separate fork step *)
      admit.
    - 
      
  Admitted. 



  Lemma client_spec Einvs (lb0: fmstate lib_fair) f
    (FB: f >= 10)
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns)
    (* (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"): *)
    (LB0_ACT: 0 ∈ live_roles _ lb0)
    (LB0_INFO: @ls_fuel _ _ lb0 !! tt = Some 2 /\ ls_under lb0 = 1 /\ ls_tmap lb0 (LM := lib_model) !! 0 = Some {[ tt ]})
    :
    PMP Einvs -∗
    {{{ partial_model_is (lb0, 2)  ∗ 
        partial_free_roles_are {[ inl 0 ]} ∗ 
        has_fuels 0 {[ inr ρy := f ]} (PMPP := PMPP)  }}}
      client #() @ 0
    {{{ RET #(); partial_mapping_is {[ 0 := ∅ ]} }}}.
  Proof using.
    iIntros "#PMP" (Φ) "!> (ST & FREE & FUELS) POST". rewrite /client.

    rewrite (sub_0_id {[ _ := _ ]}). 
    assert (fuels_ge ({[inr ρy := f]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }
    
    pure_step FS.

    wp_bind (ref _)%E.
    iApply (wp_alloc_nostep with "[$] [FUELS]").
    2: { solve_fuels_S FS. }
    { solve_map_not_empty. }
    iNext. iIntros (l) "(L & MT & FUELS) /=". 

    pure_step FS. pure_step FS.

    pose proof (live_roles_2 lb0) as LIVE2.
    pose proof (live_roles_1 lb0) as LIVE1. 
    rewrite decide_True in LIVE1; [| set_solver].

    wp_bind (_ <- _)%E.
    iApply (wp_store_step_keep with "[$] [L ST FUELS FREE]").
    { set_solver. }
    7: { iFrame "L ST FREE". iNext.
         rewrite map_fmap_singleton. iFrame. }
    { econstructor. }
    3: { rewrite dom_singleton. reflexivity. }
    2: { rewrite LIVE2 LIVE1. set_solver. } 
    2: { set_solver. }
    { Unshelve. 2: exact {[ inl 0 := lm_fl client_model (lb0, 1) ]}.
      repeat split; rewrite ?LIVE2 ?LIVE1.
      1-3, 5-7: set_solver. 
      intros. assert (ρ' = inl 0) as -> by set_solver.
      rewrite lookup_singleton. simpl. lia. }
    { set_solver. }
    iNext. iIntros "(L & ST & FUELS & FR)".
    rewrite LIVE2 LIVE1.
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { rewrite subseteq_empty_difference; [| set_solver].
      rewrite union_empty_l. reflexivity. }

    simpl. clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).    
    assert (fuels_ge ({[inl 0 := 10]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }
    
    do 2 pure_step FS. 

    iApply fupd_wp.
    iPoseProof (init_client_inv with "ST") as "inv". 
    iMod (fupd_mask_mono with "inv") as (?) "(#INV & LF & LM & LST & LFR & YST)".
    { set_solver. }
    iModIntro. 

    wp_bind (lib_fun #())%E.
    iDestruct "FUELS" as "[MAP FUELS]". 
    iApply (lib_spec with "[] [LST YST LF LM FR MAP FUELS]").
    { iApply lib_PMP; [done| ]. iSplit; done. }
    { simpl. destruct LB0_INFO as (LIBF & -> & LIBM). iFrame "LST".
      rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      simpl. iSplitR "LF".
      2: { iExists 2. iSplitR; [done| ].
           (* rewrite fuels in premise as big union by roles, use LIBF *)
           admit. }
      do 3 iExists _. iFrame. iSplitR.
      { eauto. }
      iSplitL "LM".
      { (* rewrite mapping in premise as big union by roles, use LIBM *)
        admit. }
      iLeft.
      rewrite dom_fmap_L dom_singleton_L big_sepS_singleton.
      rewrite map_fmap_singleton lookup_singleton.
      do 2 (iSplitR; [done| ]). 
      iDestruct "FUELS" as (?) "[%FF FUEL]". inversion FF.
      iExists _. iFrame. iPureIntro. rewrite /client_fl. lia. }

    iNext. iIntros "[LMAP LFR']". simpl. 
    iDestruct "LMAP" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    assert (L = ∅) as -> by set_solver.
    iDestruct "MATCH" as "[[%?] | (_&[->->]&FUEL')]"; [set_solver| ]. clear LIBM.
                                      
    (* iRename "FUELS" into "FUELS_OLD". *)
                                      
    iAssert (has_fuels 0 {[ inr ρy := 10 ]})%I with "[FUEL' MAP]" as "FUELS".
    { rewrite /has_fuels.
      rewrite !dom_singleton_L !big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }
    
    simpl. clear FS. 
    rewrite (sub_0_id {[ inr ρy := _ ]}).
    assert (fuels_ge ({[ inr ρy := 10 ]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    pure_step FS. pure_step FS.
    
    wp_bind (_ <- _)%E.

    iApply wp_atomic.
    iInv Ns as ((lb, y)) "inv" "CLOS". rewrite {1}/client_inv_impl. 
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".
    iAssert (⌜ y = 1 ⌝)%I as %->.
    { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V.
      apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. }
    iAssert (⌜ ls_tmap lb !! 0 = Some ∅ ⌝)%I as %LIB_END.
    { rewrite /lib_msi. iDestruct "inv'" as "(_&LM_AUTH&_)".
      (* TODO: use an analogue of frag_mapping_same *)
      admit. }

    pose proof (live_roles_1 lb) as LIVE1'. 
    (* rewrite !(decide_False, decide_True) in LIVE1'. -- TODO: how to do it in ssr?*)
    erewrite decide_False, decide_True in LIVE1'; eauto.
    2: { apply LM_map_empty_notlive. eauto. }    
    
    assert (live_roles client_model_impl (lb, 0) = ∅) as LIVE0.
    { simpl. rewrite /client_lr.
      apply leibniz_equiv. rewrite filter_union.
      erewrite !filter_singleton_not; [set_solver| ..].
      all: rewrite bool_decide_eq_false_2; [done| ].
      all: intros [? STEP]; inversion STEP. } 
    
    iModIntro. 
    iApply (wp_store_step_singlerole_keep with "[$] [L ST FUELS]").
    { set_solver. }
    (* { reflexivity. } *)
    5: { iFrame "L ST". iNext.
         iApply has_fuel_fuels. rewrite map_fmap_singleton. iFrame. }
    2: { by apply ct_y_step_1. }
    3: { rewrite LIVE1' LIVE0. set_solver. }
    { Unshelve. 2: exact 7. simpl. rewrite /client_fl. lia. }
    { lia. }

    (* rewrite LIVE0. erewrite decide_False; [| set_solver]. *)
    iNext. iIntros "(L & ST & FUELS)".
    iAssert (|==> y_frag_model_is 0 ∗ y_auth_model_is 0)%I with "[YST YST_AUTH]" as
      "Y".
    { admit. }
    iMod "Y" as "[YST YST_AUTH]". 
    
    iMod ("CLOS" with "[YST_AUTH ST inv']") as "_".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iModIntro.   

    iDestruct (has_fuel_fuels with "FUELS") as "FUELS". 
    simpl. clear FS. 
    rewrite (sub_0_id {[ inr ρy := _ ]}).
    assert (fuels_ge ({[ inr ρy := 7 ]}: gmap (fmrole client_model_impl) nat) 7) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    do 2 pure_step FS.

    (* TODO: restore wp_lift_pure_step_no_fork_remove_role to justify the last step *)
    admit. 
Admitted.     
    
 
End ClientSpec.

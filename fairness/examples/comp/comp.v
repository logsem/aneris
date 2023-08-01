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
                (LIB_NOSTEP: ls_tmap lb (LM := lib_model) !! 0%nat = Some ∅):
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
    let: "x" := ref #1 in
    lib_fun #() ;;
    "x" <- #0 ;;
    Skip
  .

  Instance lib_step_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof. Admitted. 
  
  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (lib_step_dec st r)))  {[ inl 0; inr ρy ]}. 
  
  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role) (s' : client_state),
    client_trans s (Some ρ) s' → ρ ∈ client_lr s.
  Proof. 
    intros ??? TRANS. rewrite /client_lr.
    apply elem_of_filter. split.
    2: { destruct ρ.
         - assert (l = 0) by admit. set_solver.
         - destruct y. set_solver. }
    rewrite bool_decide_eq_true_2; eauto.
  Admitted. 

  Definition client_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    apply client_lr_spec.
  Defined.

  Definition client_model: LiveModel heap_lang client_model_impl :=
    {| lm_fl _ := 10; |}.  

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

  Lemma init_client_inv lb0:
    partial_model_is (lb0, 2)  ={∅}=∗ 
    ∃ (cG: clientGS Σ), client_inv ∗
                        lib_frag_fuel_is (ls_fuel lb0) ∗
                        lib_frag_mapping_impl_is (ls_tmap lb0 (LM := lib_model)) ∗
                        lib_frag_model_is lb0 ∗
                        lib_frag_free_roles_are ∅ ∗
                        y_frag_model_is 2.
  Proof.
    (* simpl in lb0. red in lb0.   *)
    iIntros "ST".
    iMod (own_alloc ((● (Excl' (ls_under lb0)) ⋅ ◯ _))) as (γ_lib) "[AUTH_LIB FRAG_LIB]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }
    iMod (own_alloc ((● (Excl' 2) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }
    iMod (own_alloc ((● (Excl <$> ls_tmap lb0 (LM := lib_model)) ⋅ ◯ _ ): (authUR (gmapUR (localeO heap_lang) (exclR (gsetR (RoleO lib_model_impl))))))) as (γ_map) "[AUTH_MAP FRAG_MAP]".
    { apply auth_both_valid_discrete. split; [reflexivity|].
      (* eapply gmap_validI.  *)
      admit. } 
    iMod (own_alloc (((● (Excl <$> ls_fuel lb0)) ⋅ ◯ _): (authUR (gmapUR (RoleO lib_model_impl) (exclR natO))))) as (γ_fuel) "[AUTH_FUEL FRAG_FUEL]".
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      (* eapply gmap_validI.  *)
      admit. 
    }
    iMod (own_alloc ((● (∅: gset_disj (fmrole lib_model_impl))  ⋅ ◯ _ ): authUR (gset_disjUR (RoleO lib_model_impl)))) as (γ_fr) "[AUTH_FR FRAG_FR]".
    { apply auth_both_valid_2 =>//.
      (* done. *)
      admit. }

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
  Admitted. 
    

  Lemma client_spec Einvs lb0 f
    (FB: f >= 10):
    (* TODO: get rid of these restrictions *)
    (* (DISJ_INV1: Einvs ## ↑Ns) (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"): *)
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

    iApply (fupd_wp ∅).
    iPoseProof (init_client_inv with "ST") as "inv". 
    iMod (fupd_mask_mono with "inv") as (?) "(#INV & LF & LM & LST & LFR & YST)".
    { set_solver. }
    iModIntro. 

    wp_bind (lib_fun #())%E.
    iApply lib_spec. 
    
    
    
 
End ClientSpec.

From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fuel_ext resources actual_resources.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import utils.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext.
From trillium.fairness.heap_lang Require Export lang lm_lsi_hl_wp tactics proofmode_lsi.

Close Scope Z_scope.

Section ClientDefs.

  Let lib_st := fmstate lib_fair.
  (* Let lib_role := fmrole lib_fair. *)
  Let lib_erole := @ext_role _ ExtLibLM. 

  Definition client_state: Type := lib_st * nat.

  Inductive y_role := ρy.
  Definition client_role: Type := lib_erole + y_role.

  Definition ρ_cl: client_role := inr ρy.
  Definition ρ_lib: client_role := inl $ inl ρlg.
  Definition ρ_ext: client_role := inl $ inr $ env (eiG ρlg) (EM := ExtLibLM). 
  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_y_step_3 lb:
    client_trans (lb, 3) (Some ρ_cl) (lb, 2)
  (* TODO: allow arbitrary library's LM roles *)
  | ct_lib_ext lb1 lb2 (LIB_EXT: reset_lm_st_rel ρlg lb1 lb2):
    client_trans (lb1, 2) (Some ρ_ext) (lb2, 1)
  | ct_lib_step lb1 lb2 (LIB_STEP: fmtrans lib_fair lb1 (Some ρlg) lb2):
    client_trans (lb1, 1) (Some ρ_lib) (lb2, 1)
  | ct_y_step_1 (lb: fmstate lib_fair)
                (* (LIB_NOSTEP: 0 ∉ live_roles _ lb) *)
                (LIB_NOROLES: ls_tmap lb (LM := lib_model) !! ρlg = Some ∅)
    :
    client_trans (lb, 1) (Some ρ_cl) (lb, 0)
  .

  Global Instance lib_role_EqDec: EqDecision lib_erole.
  Proof. solve_decision. Defined.
  Global Instance lib_role_Cnt: Countable lib_erole.
  Proof using.
    rewrite /lib_erole. simpl. apply _.
  Defined.
  
  Instance y_EqDec: EqDecision y_role.
  Proof. by (solve_decision). Qed.

  Global Instance client_role_Cnt: Countable client_role.
  Proof using.
    rewrite /client_role.
    unshelve eapply sum_countable.
    eauto. eapply (inj_countable' (fun _ => ()) (fun _ => ρy)).
    by destruct x.
  Qed.

  Definition client: val :=
  λ: <>,
    let: "x" := ref #2 in
    "x" <- #1 ;;
    lib_fun #() ;;
    "x" <- #0 ;;
    Skip
  .

  (* Instance lib_step_dec (st: client_state) (ρ: client_role) st': *)
  (*   Decision (client_trans st (Some ρ) st'). *)
  (* Proof. *)
  (*   Local Ltac nostep := right; intros T; inversion T. *)
  (*   destruct st as [δ_lib n], st' as [δ'_lib n']. *)
  (*   destruct (decide (n = S n' /\ ρ = inr ρy /\ δ_lib = δ'_lib)), *)
  (*            (decide (n = 1 /\ n' = 1 /\ ρ = inl ρlg)). *)
  (*   { lia. } *)
  (*   3: { nostep; subst; tauto. } *)
  (*   - destruct a as (->&->&<-). *)
  (*     destruct n'; [| destruct n'].  *)
  (*     + destruct (ls_tmap δ_lib (LM := lib_model) !! ρlg) eqn:LIB_OBLS. *)
  (*       2: { nostep. by rewrite LIB_OBLS in LIB_NOROLES. } *)
  (*       destruct (decide (g = ∅)). *)
  (*       * subst. left. by constructor.  *)
  (*       * nostep. rewrite LIB_OBLS in LIB_NOROLES. set_solver. *)
  (*     + left. econstructor. *)
  (*     + nostep. *)
  (*   - destruct a as (->&->&->). *)
  (*     destruct (decide (locale_trans δ_lib ρlg δ'_lib (LM := lib_model))).  *)
  
  Instance client_step_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof.
    Local Ltac nostep := right; intros [? T]; inversion T.
    destruct st as [δ_lib n]. destruct n; [| destruct n]; [..| destruct n]; [..| destruct n]. 
    - by nostep. 
    - destruct ρ.
      + destruct l.
        2: by nostep. 
        destruct f. 
        destruct (decide (exists δ'_lib, locale_trans δ_lib () δ'_lib (LM := lib_model))).
        ** left. destruct e. eexists. econstructor. simpl. eauto.
        ** nostep. simpl in LIB_STEP. eauto. 
      + destruct y. 
        destruct (ls_tmap δ_lib (LM := lib_model) !! ρlg) eqn:LIB_OBLS.
        2: { nostep. by rewrite LIB_OBLS in LIB_NOROLES. }
        destruct (decide (g = ∅)).
        * subst. left. eexists. by constructor. 
        * nostep. rewrite LIB_OBLS in LIB_NOROLES. set_solver.
    - destruct ρ; [destruct l| ]. 
      1, 3: by nostep. 
      destruct e. destruct (decide (i ∈ active_exts δ_lib)).
      + left. destruct i. 
        apply active_exts_spec in e as [??]. simpl in *. 
        eexists. destruct ρlg. 
        eapply ct_lib_ext; eauto.
      + nostep. subst. apply n. apply active_exts_spec.
        inversion T. subst. simpl. eauto.
    - destruct ρ.
      + nostep.
      + destruct y. left. eexists. constructor.
    - nostep. 
  Qed.

  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (client_step_dec st r) = true))  
      {[ ρ_lib; ρ_ext; ρ_cl ]}. 

  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role),
      (exists s', client_trans s (Some ρ) s') <-> ρ ∈ client_lr s.
  Proof.
    intros ??. rewrite /client_lr.
    rewrite elem_of_filter. rewrite @bool_decide_eq_true.
    rewrite !elem_of_union. rewrite !elem_of_singleton. 
    split.
    2: tauto. 
    intros [? TRANS]. split; eauto. inversion TRANS; subst; eauto.
  Qed.

  Definition client_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    - intros. eapply client_lr_spec; eauto. 
  Defined.

  
    (* forall k δo_k gi, lmtr_o S!! k = Some δo_k -> *)
    (*              (exists (δi: LiveState Gi Mi LSIi) (ρi: fmrole Mi), *)
    (*                 state_rel (ls_under δo_k) δi /\ *)
    (*                 ls_mapping δi !! ρi = Some gi) -> *)
    (*              lift_Gi gi ∈ dom (ls_mapping δo_k).  *)
  Definition client_LSI (s: client_state)
    (m: gmap (fmrole client_model_impl) (locale heap_lang))
    (_: gmap (fmrole client_model_impl) nat) :=
    forall gi, (exists ρi, ls_mapping s.1 !! ρi = Some gi) -> inl $ inl gi ∈ dom m.
    
  Definition client_fl := 15. 
  Definition client_model: LiveModel (locale heap_lang) client_model_impl client_LSI :=
    {| lm_fl _ := client_fl; |}.  

  Class clientPreGS (Σ: gFunctors) := ClientPreGS {
     cl_pre_y_st :> inG Σ (authUR (optionR (exclR natO)));
     cl_lib_preΣ :> fairnessGpreS lib_model Σ;
  }.

  Class clientGS Σ := ClientGS {
    cl_pre_inG :> clientPreGS Σ;
    cl_y_st_name : gname;
    cl_lib_Σ :> fairnessGS lib_model Σ;
  }.

End ClientDefs. 

Section ClientRA.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cG: clientGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.
  
  Notation "'lib_inn_role'" := (fmrole lib_model_impl).
  Notation "'lib_inn_state'" := (fmstate lib_model_impl).
  Notation "'lib_state'" := (fmstate lib_fair).

  Definition y_auth_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (● Excl' y).

  Definition y_frag_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (◯ Excl' y).

  Definition client_inv_impl (st: client_state) : iProp Σ :=
    let (lb, y) := st in
    partial_model_is st ∗
    y_auth_model_is y ∗
    (* lib_msi lb.  *)
    model_state_interp lb (fG := cl_lib_Σ).

  Definition Ns := nroot .@ "client".

  Definition client_inv: iProp Σ :=
    inv Ns (∃ (st: client_state), client_inv_impl st).

End ClientRA.


Section ClientSpec.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cpG: clientPreGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.

  (* Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS))). *)
  Notation "'LSG' Einvs" := (LM_steps_gen Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS)) (at level 10).

  (* TODO: remove tid=0 restriction ? *)
  Let lib_pmi `{clientGS Σ} (m: gmap (locale heap_lang) (gset (fmrole lib_model_impl))): iProp Σ:=
    (∃ (L: gset (fmrole lib_model_impl)) (Ract Rfr: gset client_role),
        ⌜ m = {[ 0 := L ]} ⌝ ∗
         frag_mapping_is {[ ρlg := L ]} ∗
         (⌜ L ≠ ∅ ⌝ ∗ ⌜ Ract = {[ ρ_lib ]} /\ Rfr = {[ ρ_cl ]} ⌝ ∗ (∃ f: nat, partial_fuel_is {[ ρ_lib := f ]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∨
          ⌜ L = ∅ ⌝ ∗ ⌜ Ract = {[ ρ_cl ]} /\ Rfr = {[ ρ_lib ]} ⌝ ∗ partial_fuel_is {[ inr ρy := client_fl ]}) ∗
        partial_mapping_is {[ 0 := Ract ]} ∗
        partial_free_roles_are Rfr ∗
        y_frag_model_is 1).
  
  Definition lib_PMPP `{clientGS Σ}:
    @PartialModelPredicatesPre (locale heap_lang) _ _ Σ lib_model_impl.
   refine
    {|
        partial_model_is := frag_model_is;
        partial_free_roles_are := frag_free_roles_are;
        partial_fuel_is := frag_fuel_is;
        partial_mapping_is := lib_pmi;
    |}.
  Unshelve.
  all: try (apply _ || solve_proper).
  (* TODO: reuse proofs from resources.v *)
  - intros.
    rewrite /frag_fuel_is.
    rewrite map_fmap_union. rewrite -gmap_disj_op_union.
    2: { by apply map_disjoint_fmap. }
    by rewrite auth_frag_op own_op.
  - intros. rewrite /frag_free_roles_are.
    rewrite -gset_disj_union; auto.
    by rewrite auth_frag_op own_op.
  - iApply own_unit.
  Defined.

  Definition lib_spec_pre `{clientGS Σ} tid: iProp Σ :=
    partial_model_is 1 (PartialModelPredicatesPre := lib_PMPP) ∗
    has_fuels tid {[ ρl:=2 ]} (PMPP := lib_PMPP).

  Definition lib_spec_post `{clientGS Σ} tid: iProp Σ :=
    partial_mapping_is {[ tid := ∅ ]} (PartialModelPredicatesPre := lib_PMPP) ∗
    partial_free_roles_are {[ ρl ]} (PartialModelPredicatesPre := lib_PMPP).

  (* TODO: move to library, weaken Σ requirement *)
  Lemma lib_premise `{clientGS Σ} (lb: lm_ls lib_model)
    (LB_INFO: lib_ls_premise lb):
    ⊢ (frag_model_is (ls_under lb) -∗ frag_fuel_is (ls_fuel lb) -∗ frag_mapping_is (ls_tmap lb) -∗
    frag_model_is (1: fmstate lib_model_impl) ∗ frag_mapping_is {[ρlg := {[ρl]}]} ∗ frag_fuel_is {[ρl := 2]})%I.
  Proof.
    iIntros "LST LF LM".
    destruct LB_INFO as (LIBF & -> & LIBM).
    iFrame "LST". iSplitL "LM".
    { rewrite -frag_mapping_is_big_sepM.
      2: { intros E. by rewrite E in LIBM. }
      erewrite big_opM_insert_delete'; eauto.
      iDestruct "LM" as "[??]". iFrame. }
    rewrite -frag_fuel_is_big_sepM.
    2: { intros E. by rewrite E in LIBF. }
    erewrite big_opM_insert_delete'; eauto.
    iDestruct "LF" as "[??]". iFrame.
  Qed.

  Lemma init_client_inv lb0 n:
    partial_model_is (lb0, n)  ={∅}=∗
    ∃ (cG: clientGS Σ), client_inv ∗
                        frag_fuel_is (ls_fuel lb0) (fG := cl_lib_Σ) ∗
                        frag_mapping_is (ls_tmap lb0 (LM := lib_model)) (fG := cl_lib_Σ)∗
                        frag_model_is lb0 (fG := cl_lib_Σ)∗
                        frag_free_roles_are ∅ (fG := cl_lib_Σ)∗
                        y_frag_model_is n.
  Proof using cpG.
    iIntros "ST".
        
    iMod (lm_msi_init lb0 ∅) as (fG) "(MSI_LIB & FRAG_LIB & FRAG_MAP & FRAG_FUEL & FRAG_FR)".
    { set_solver. }

    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

    set (cG := {|
                cl_pre_inG := cpG;
                cl_y_st_name := γ_st;
                cl_lib_Σ := fG;
              |}).
 
    iMod (inv_alloc Ns _  (∃ st, client_inv_impl st) with "[-FRAG_LIB FRAG_Y FRAG_MAP FRAG_FR FRAG_FUEL]") as "#INV".
    { iNext. rewrite /client_inv_impl.
      iExists (_, _). iFrame. }

    iModIntro. iExists _. iFrame. done.
  Qed.

  Lemma live_roles_1 lb:
    live_roles client_model_impl (lb, 1) =
    if (decide (ρlg ∈ live_roles _ lb))
    then {[ ρ_lib ]}
    else if decide (ls_tmap lb (LM := lib_model) !! ρlg = Some ∅)
         then {[ ρ_cl ]}
         else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.

    erewrite filter_singleton_not with (x := ρ_ext). 
    2: { rewrite bool_decide_eq_false_2; [done| ].
         intros [? STEP]. inversion STEP. }
    rewrite union_empty_r. 

    destruct (decide (ρlg ∈ live_roles lib_fair lb)) as [LR | LR].
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
      destruct (ls_tmap lb (LM := lib_model) !! ρlg) eqn:MAP0.
      (* ; rewrite MAP0. *)
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

  Lemma live_roles_3 lb0:
    live_roles client_model_impl (lb0, 3) ≡ {[ ρ_cl ]}.
  Proof.
    simpl. rewrite /client_lr.
    rewrite !filter_union.
    erewrite filter_singleton_not, filter_singleton_not, filter_singleton; [set_solver| ..].
    - rewrite bool_decide_eq_true_2; [done| ]. eexists. econstructor.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
  Qed.

  Lemma live_roles_0 lb:
    live_roles client_model_impl (lb, 0) = ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    erewrite !filter_singleton_not; [set_solver| ..].
    all: rewrite bool_decide_eq_false_2; [done| ].
    all: intros [? STEP]; inversion STEP.
  Qed.

  (* TODO: move *)
  Lemma set_filter_equiv:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (P_EQ: forall x, P1 x <-> P2 x)
    (c1 c2: C)
    (EQUIV: c1 ≡ c2)
    ,
    filter P1 c1 = filter P2 c2.
  Proof. set_solver. Qed.

  (* TODO: move *)
  Lemma set_filter_and:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C)
    ,
    filter P1 (filter P2 c) = filter (fun x => P1 x /\ P2 x) c.
  Proof. set_solver. Qed. 

  (* TODO: move *)
  Lemma set_filter_comm:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C)
    ,
    filter P1 (filter P2 c) = filter P2 (filter P1 c). 
  Proof. set_solver. Qed. 

  (* TODO: move *)
  Lemma filter_singleton_if:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ (P : A → Prop) {H7 : ∀ x : A, Decision (P x)} (x : A),
        filter P ({[x]} : C) ≡ if decide (P x) then {[x]} else ∅.
  Proof. intros. destruct decide; set_solver. Qed. 


  Lemma live_roles_2 lb:
    live_roles client_model_impl (lb, 2) =
    if (decide (lm_is_stopped ρlg lb))
    then {[ ρ_ext ]}
    else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    rewrite union_comm.
    rewrite filter_singleton_not; [rewrite filter_singleton_not| ].
    2, 3: rewrite bool_decide_eq_false_2; [done| ]; 
    intros [? STEP]; by inversion STEP.
    rewrite !union_empty_l.

    unshelve erewrite set_filter_equiv with (P2 := fun r => r = ρ_ext /\ lm_is_stopped ρlg lb).
    5: reflexivity. 
    { intros. apply and_dec.
      - (* TODO: infer automatically *)
        destruct x, ρ_ext.
        { destruct e, e0.
          { destruct (decide (f = f0)); [left | right]; congruence. }
          3: destruct (decide (e = e0)); [left | right]; congruence.
          all: right; intros ?; congruence. }
        3: { destruct (y_EqDec y y0); [left | right]; congruence. }
        all: right; intros ?; congruence. 
      - solve_decision. }
    2: { intros. rewrite bool_decide_eq_true.
         split.
         - intros [? STEP]. inversion STEP. subst. split; eauto.
           red in LIB_EXT. rewrite /reset_lm_st in LIB_EXT.
           destruct decide; done.
         - intros [-> STOP]. exists ((reset_lm_st_impl ρlg lb STOP), 1). econstructor.
           red. rewrite /reset_lm_st. destruct decide; [| done].
           done. }

    rewrite -set_filter_and set_filter_comm.
    erewrite set_filter_equiv.
    3: { rewrite filter_singleton; reflexivity. }
    2: { intros. apply iff_refl. }
    rewrite filter_singleton_if. 
    repeat destruct decide; reflexivity || tauto.
    Unshelve. intros. solve_decision. 
  Qed. 
    

  Tactic Notation "specialize_full" ident(H) :=
    let foo := fresh in
    evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].


  (* TODO: make it a library LSI *)
  Lemma lib_tmap_dom_restricted (δ: fmstate lib_fair):
    dom (ls_tmap δ (LM := lib_model)) ⊆ {[ ρlg ]}.
  Proof. Admitted.

  Lemma update_client_state `{clientGS Σ} Einvs
    (extr: execution_trace heap_lang) (mtr: auxiliary_trace M)
    c2 (lb lb': fmstate lib_fair) f
    (LIB_STEP: locale_trans lb ρlg lb' (LM := lib_model))
    (PROG_STEP: locale_step (trace_last extr) (Some 0) c2)
    (F_BOUND: f ≤ client_fl)
    :
    LSG Einvs ⊢
    em_msi (trace_last extr) (trace_last mtr) (em_GS0 := heap_fairnessGS) -∗
    partial_model_is (lb, 1) -∗
    partial_free_roles_are {[ρ_cl]} -∗
    has_fuels 0 {[ρ_lib := f]}
    ={Einvs}=∗
    ∃ (δ2 : M) (ℓ: mlabel M),
      ⌜em_valid_evolution_step (Some 0) c2 (trace_last mtr) ℓ δ2⌝ ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS) ∗
      has_fuels 0 (if decide (ls_tmap lb' (LM := lib_model) !! ρlg = Some ∅)
                   then {[ρ_cl := client_fl]}
                   else {[ρ_lib := f]}) ∗
      partial_model_is (lb', 1) ∗
      partial_free_roles_are
      (if decide (ls_tmap lb' (LM := lib_model) !! ρlg = Some ∅) then {[ρ_lib]} else {[ρ_cl]}).
  Proof.
    
    iIntros "#PMP MSI ST FR FUELS".
    Local Ltac dEq := destruct (decide (_ = _)).
    Local Ltac dEl := destruct (decide (_ ∈ _)).
    pose proof (LM_map_empty_notlive lb' ρlg (LM := lib_model)).

    pose proof (live_roles_1 lb) as LIVE. rewrite decide_True in LIVE.
    2: { eapply LM_live_roles_strong. eexists. eauto. }
    (* TODO: consider the case with rem ≠ ∅ *)
    pose proof (live_roles_1 lb') as LIVE'.

    remember (trace_last extr) as c1. destruct c1 as (σ1, tp1).
    destruct c2 as (σ2, tp2).

    iPoseProof (update_step_still_alive_gen with "[$] [$] [$] [$] [$]") as "EM_STEP".
    7: { apply PROG_STEP. }
    7: { apply ct_lib_step. simpl. eauto. }
    { rewrite LIVE LIVE'.
      apply union_subseteq_l'.
      dEq; dEl; set_solver. }
    { rewrite dom_singleton.
      assert ((if (decide (ls_tmap lb' (LM := lib_model) !! ρlg = Some ∅))
              then {[ ρ_lib ]}
              else (∅: gset (fmrole client_model_impl))) ⊆ {[ρ_lib]}) as IN.
      { dEq; set_solver. }
      apply IN. }
    { rewrite LIVE. set_solver. }
    all: eauto.
    { Unshelve.
      2: exact (if decide (ls_tmap lb' (LM := lib_model) !! ρlg = Some ∅)
                then {[ ρ_cl := client_fl ]}
                else {[ ρ_lib := f ]}).
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
        intros. assert (ρ' = ρ_cl) as -> by set_solver.
        rewrite lookup_singleton. simpl. lia.
      - dEq; set_solver.
      - dEq; dEl; set_solver.
      - dEq; dEl; set_solver. }
    { red. intros. red.
      (* TODO: move this simplification, as it occurs quite often *)
      rewrite /update_mapping. rewrite map_imap_dom_eq.
      2: { rewrite dom_gset_to_gmap. intro.
           destruct (decide (k ∈ dom R)); [| done].
           intros. by eapply elem_of_dom. }
      rewrite dom_gset_to_gmap. intros g' IN'.
      red in H2.
      (* at this point we must ensure that no new group roles  *)
(*          were created by a lib step *)

      destruct IN' as [? IN']. simpl in IN'.
      apply (ls_mapping_tmap_corr (LM := lib_model)) in IN' as (?&?&?).
      pose proof (lib_tmap_dom_restricted lb') as DOML.
      specialize (DOML g'). specialize_full DOML.
      { apply elem_of_dom. set_solver. }
      apply elem_of_singleton_1 in DOML. subst g'.
      rewrite decide_False; [set_solver| ].
      intros EMP. set_solver. }
      
    rewrite LIVE LIVE'.
    iMod "EM_STEP" as (??) "(?&?&?&?&FREE)".
    iModIntro. do 2 iExists _. iFrame.
    
    iApply partial_free_roles_are_Proper; [| iFrame].
    dEl; dEq; tauto || set_solver.
  Qed.

  (* TODO: unify with model_agree ? *)
  Lemma y_model_agree `{clientGS Σ} y1 y2:
    ⊢ y_auth_model_is y1 -∗ y_frag_model_is y2 -∗ ⌜y1 = y2⌝.
  Proof.
    iIntros "Ha Hf".
    by iDestruct (own_valid_2 with "Ha Hf") as
      %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  (* TODO: unify with update_model ? *)
  Lemma y_update_model `{clientGS Σ} y1 y2 y:
    y_auth_model_is y1 -∗ y_frag_model_is y2 ==∗ y_auth_model_is y ∗ y_frag_model_is y.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl y)).
    - iModIntro. iFrame.
  Qed.
     
(*   Lemma big_opM_fmap': *)
(*   ∀ {M M' : ofe} {o : M → M → M} {o' : M' → M' → M'} *)
(*     {Monoid0 : Monoid o} {Monoid0' : Monoid o'} {K : Type} *)
(*     {EqDecision0 : EqDecision K} {H : Countable K} *)
(*     (f : M → M') (m : gmap K M), *)
(*     (([^ op map] k↦y ∈ m, f <$> ({[ k := y ]}: gmap K M)): gmap K M') = (f <$> m: gmap K M'). *)
(* (* f <$> {[k := ]} *) *)


  Lemma lib_open_inv `{clientGS Σ} ζ fs (FSnz : fs ≠ ∅):
    client_inv -∗ has_fuels ζ fs (PMPP := lib_PMPP) -∗
    |={↑Ns, ∅}=>
    ⌜ ζ = 0 ⌝ ∗
    (∃ lb, partial_model_is (lb, 1) (PartialModelPredicatesPre := PMPP) ∗ model_state_interp lb) ∗
    frag_mapping_is {[ρlg := dom fs]}  ∗ y_auth_model_is 1 ∗
    (∃ f, partial_fuel_is {[ρ_lib := f]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∗
    partial_mapping_is {[0 := {[ρ_lib]}]} ∗
    partial_free_roles_are {[inr ρy]} ∗ y_frag_model_is 1 ∗
    frag_fuel_is fs ∗
    (▷ (∃ st, client_inv_impl st) ={ ∅, ↑Ns}=∗ emp).
  Proof.
    iIntros "#INV FUELS_LIB".
    iInv Ns as ((lb, y)) ">(ST & YST_AUTH & inv')" "CLOS".
    rewrite difference_diag_L. iModIntro.
    iDestruct (has_fuels_equiv with "FUELS_LIB") as "[MAP_LIB FUEL_LIB]".
    simpl. iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    assert (ζ = 0 /\ L = dom fs) as [-> ->]; [| clear LIBM].
    { by apply map_singleton_inj in LIBM as [-> <-]. }
    (* assert (S <$> fs ≠ ∅) by (by intros ?%fmap_empty_inv). *)
    iDestruct "MATCH" as "[(_&[-> ->]&(%f & Ff & %BOUND)) | [% _]]".
    2: { exfalso. apply FSnz. apply dom_empty_iff. set_solver. }
    iPoseProof (y_model_agree with "YST_AUTH YST") as "->".
    iPoseProof (frag_mapping_same with "[inv'] LM") as "%TMAP0".
    { iDestruct "inv'" as (?)"(?&?&?)". iFrame. }
    iPoseProof (frag_fuel_included with "[inv'] [FUEL_LIB]") as "%FUEL0".
    { iDestruct "inv'" as (?)"(?&?&?&?)". iFrame. }
    { iApply frag_fuel_is_big_sepM; [done | by iFrame]. }
    iSplitR; [done| ].
    iFrame. iSplitL "ST inv'".
    - iExists _. iFrame.
    - iDestruct (frag_fuel_is_big_sepM with "FUEL_LIB") as "?"; [done| ].
      iFrame. iExists _. iFrame. done.
  Qed.


  Lemma fuel_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  LSG Einvs ∗ client_inv ⊢
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
    
    assert (S <$> fs ≠ ∅) as NE.
    { intros ?%dom_empty_iff. set_solver. }

    iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [set_solver| ].
    rewrite union_comm_L.
    iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as
      "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ].
    
    iMod (actual_update_no_step_enough_fuel with "[LM FUEL_LIB] inv'") as (lb') "(%LIB_STEP & FUELS_LIB & MSI_LIB & %TMAP_LIB)".
    3: { apply empty_subseteq. }
    { eauto. }
    { set_solver. }
    { rewrite /has_fuels_S. rewrite has_fuels_equiv. iFrame.
      iApply frag_fuel_is_big_sepM; done. }
    
    destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2).
    rewrite LASTE.
    rewrite difference_empty_L. rewrite difference_empty_L in TMAP_LIB.
    iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -LASTE.
    iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto.
    { eexists. split; [apply LIB_STEP| ]. done. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".

    iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ].

    iModIntro.
    iDestruct "FUELS" as "[MAP FUEL]". iDestruct "FUELS_LIB" as "[MAP_LIB FUELS_LIB]".
    rewrite /has_fuels. iSplitR "FUELS_LIB".
    2: { rewrite dom_domain_restrict; [| set_solver]. done. }
    simpl. rewrite dom_domain_restrict; [| set_solver].
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done| ].
    (* TODO: case when domain becomes empty *)
    iLeft. iSplitR; [done| ].
    rewrite TMAP_LIB. rewrite lookup_insert.
    repeat erewrite @decide_False with (P := (Some (dom fs) = Some ∅)).
    2-3: by intros [=].
    iSplitR.
    - iPureIntro. set_solver.
    - rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton.
      iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst.
      iExists _. iFrame. iPureIntro. lia.
  Qed.
  
  Lemma model_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  LSG Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M)
    (tp1 tp2 : list (language.expr heap_lang)) (σ1 σ2 : language.state heap_lang)
    (s1 s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat)
    (ρ : fmrole lib_model_impl) (δ1 : M) (ζ : locale heap_lang)
    (fr1 fr_stash : gset (fmrole lib_model_impl))
    (_ : live_roles lib_model_impl s2 ∖ live_roles lib_model_impl s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
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
        (fr1 ∖ (live_roles lib_model_impl s2 ∖ (live_roles lib_model_impl s1 ∪ dom fs1 ∩ dom fs2))
         ∪ fr_stash) (PartialModelPredicatesPre := lib_PMPP).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI FR_LIB". simpl in *.
    
    assert (ρ ∈ dom fs1) as DOM1ρ by apply x7.
    assert (dom fs1 ≠ ∅ /\ fs1 ≠ ∅) as [FS1nz FS1nz'].
    { split; intros ?; set_solver. }
    
    iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [done| ].
    rewrite union_comm_L.
    iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as
      "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ].
    
    iMod (actual_update_step_still_alive with "[LM FUEL_LIB] [$] [$] [$]") as "LIFT"; eauto.
    { rewrite has_fuels_equiv. iFrame. iApply frag_fuel_is_big_sepM; done. }
    iDestruct "LIFT" as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & FR_LIB & %TMAP_LIB)".
    simpl. iFrame "ST_LIB".
    
    iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -x3 -x4. rewrite -x3 in x5.
    iPoseProof (update_client_state with "[$] [MSI] [ST] [$] [$]") as "EM_STEP"; eauto.
    { eexists. split; [apply LIB_STEP| ]. done. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".

    iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ].
    iModIntro.

    rewrite !has_fuels_equiv. simpl.
    iDestruct "FUELS" as "[MAP FUELS]".
    iDestruct "FUELS_LIB" as "[MAP' FUELS_LIB]". iFrame "FUELS_LIB FR_LIB".
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done |].
    rewrite TMAP_LIB. rewrite lookup_insert.
    dEq.
    - iRight. rewrite big_sepM_singleton. iFrame.
      iPureIntro. set_solver.
    - iLeft. rewrite big_sepM_singleton.
      iApply bi.sep_assoc. iSplitR "FUELS".
      2: { iExists _. iFrame. iPureIntro. lia. }
      iPureIntro. split; [| set_solver]. intros ?. rewrite H1 in n. done.
  Qed.


  Lemma lib_PMP `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
    LSG Einvs ∗ client_inv ⊢
    (* PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl1_PMPP γ)).  *)
    PartialModelPredicates (Einvs ∪ ↑Ns) (EM := EM) (iLM := lib_model) (PMPP := lib_PMPP) (eGS := heap_fairnessGS).
  Proof.
    iIntros "[#PMP #COMP]". iApply @Build_PartialModelPredicates.

    iModIntro. repeat iSplitR.
    - iIntros "* FUELS_LIB MSI".
      iDestruct (fuel_step_lifting with "[$] [] [] FUELS_LIB MSI") as "LIFT"; eauto.
      (* change the PMP interface so it allows fupd in fuel step *)
      admit.
    - (* TODO: shouldn't be required from a library that doesn't fork *)
      admit.
    - iIntros "* FUELS_LIB ST MSI FR".
      iApply (model_step_lifting with "[$] [] [] [] [] [] [] [] [] [] [$] [$] [$] [$]"); eauto.
  Admitted.

  (* TODO: problems with Countable instance *)
  (* Set Printing All. *)
  (* Lemma fuel_reorder_preserves_client_LSI: *)
  (*   fuel_reorder_preserves_LSI (LSI := client_LSI).  *)
  Lemma fuel_reorder_preserves_client_LSI:
    @fuel_reorder_preserves_LSI (locale heap_lang) client_model_impl client_LSI.
  Proof.
    red. rewrite /client_LSI. intros. set_solver.
  Qed.


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
    [| rewrite -map_fmap_compose; (try rewrite sub_comp); by iFrame];
    solve_fuels_ge_1 FS.

  Ltac solve_map_not_empty := intros ?MM%fmap_empty_iff; try rewrite -insert_empty in MM; try apply insert_non_empty in MM; set_solver.

  Ltac pure_step_impl FS :=
    try rewrite sub_comp;
    iApply wp_lift_pure_step_no_fork; auto;
    [| iSplitR; [done| ]; do 3 iModIntro; iSplitL "FUELS"];
    [| solve_fuels_S FS |];
    (* [by intros ?%fmap_empty_iff| ]; *)
    [solve_map_not_empty| ];
    iIntros "FUELS"; simpl; try rewrite sub_comp.

  Ltac pure_step FS :=
    unshelve (pure_step_impl FS); [by apply fuel_reorder_preserves_client_LSI| ].

  (* TODO: move, upstream *)
  Lemma dom_filter_comm {K A: Type} `{Countable K}
                        (P: K -> Prop) `{∀ x : K, Decision (P x)}:
    forall (m: gmap K A), dom (filter (fun '(k, _) => P k) m) = filter P (dom m).
  Proof.
    intros. apply leibniz_equiv. apply dom_filter. intros.
    rewrite elem_of_filter elem_of_dom.
    rewrite /is_Some. split; [intros [?[??]] | intros [? [??]]]; eauto.
  Qed.

  (* TODO: move *)
  Lemma lib_reset_premise g lb STOP:
    lib_ls_premise (reset_lm_st_impl g lb STOP).
  Proof. 
    red. repeat split; simpl.
    - (* TODO: fix required fuel amount in lib_ls_premise *)
      admit.
    - (* TODO: reformulate reset_lm_st_impl via ls_tmap *)
      admit.
  Admitted. 


Lemma client_spec (Einvs: coPset) (lb0: fmstate lib_fair) f
    (FB: f >= client_fl)
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns)
    (* (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"): *)
    
    (* (LB0_INFO: lib_ls_premise lb0) *)
    (LB0_INFO: lm_is_stopped ρlg lb0)
    :
    LSG Einvs -∗
    {{{ partial_model_is (lb0, 3)  ∗
        partial_free_roles_are {[ ρ_lib; ρ_ext ]} ∗
        has_fuels 0 {[ ρ_cl := f ]} (PMPP := PMPP)  }}}
      client #() @ 0
    {{{ RET #(); partial_mapping_is {[ 0 := ∅ ]} }}}.
  Proof using cpG.
    unfold client_fl in *.
    iIntros "#PMP" (Φ) "!> (ST & FREE & FUELS) POST". rewrite /client.

    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_cl := f]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    pure_step FS.

    wp_bind (ref _)%E.
    iApply (wp_alloc_nostep with "[$] [FUELS]").
    2: { solve_fuels_S FS. }
    { solve_map_not_empty. }
    iNext. iIntros (l) "(L & MT & FUELS) /=".
    Unshelve. 2: by apply fuel_reorder_preserves_client_LSI.

    pure_step FS. pure_step FS.
    (* Set Printing Implicit. Unshelve. *)

    pose proof (live_roles_3 lb0) as LIVE3.
    pose proof (live_roles_2 lb0) as LIVE2.
    rewrite decide_True in LIVE2; [ | done].

    wp_bind (_ <- _)%E.
    iApply (wp_store_step_keep with "[$] [L ST FUELS FREE]").
    { set_solver. }
    8: { iFrame "L ST FREE". iNext.
         rewrite map_fmap_singleton. iFrame. }
    { econstructor. }
    3: { rewrite dom_singleton. reflexivity. }
    2: { rewrite LIVE3 LIVE2.
         apply union_subseteq_l'. set_solver. }
    2: { set_solver. }
    { Unshelve. 2: exact {[ ρ_ext := lm_fl client_model (lb0, 2) ]}.
      repeat split; rewrite ?LIVE3 ?LIVE2.
      1-3, 5-7: set_solver.
      intros. assert (ρ' = ρ_ext) as -> by set_solver.
      rewrite lookup_singleton. simpl. lia. }
    { set_solver. }
    { red. intros. simpl. red.
      intros.
      (* assert (client_LSI (lb0, 2) M0 F) as LSI1 by admit. *)
      (* red in LSI1. *)
      rewrite /update_mapping. rewrite map_imap_dom_eq.
      2: { intros. destruct decide; [| done].
           by apply elem_of_dom. }
      rewrite dom_gset_to_gmap.
      rewrite !dom_singleton.
      assert (gi = ρlg) as ->.
      { by destruct gi, ρlg. }
      set_solver. }

    iNext. iIntros "(L & ST & FUELS & FR)".
    rewrite LIVE3 LIVE2.
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { rewrite !dom_singleton.
      Unshelve. 2: exact ({[ρ_lib; ρ_cl]}). set_solver. }

    simpl. clear FS.
    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_ext := client_fl]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. unfold client_fl.
      intros ??[? ?]%lookup_singleton_Some. lia. }

    do 1 pure_step FS.

    set (lb' := reset_lm_st_impl ρlg lb0 LB0_INFO). 
    pose proof (live_roles_1 lb') as LIVE1.
    rewrite decide_True in LIVE1.
    2: { apply lib_premise_dis. apply lib_reset_premise. }
           
    iApply (wp_lift_pure_step_no_fork_take_step_stash).
    { done. }
    (* { reflexivity. } *)
    9: iSplitL "PMP"; [by iApply "PMP"| ]; iFrame "ST FUELS FR".
    { set_solver. }
    3: { rewrite dom_fmap dom_singleton. reflexivity. }
    5: { econstructor. red. rewrite /reset_lm_st.
         destruct decide; [| done].
         Unshelve.
         2: exact ⊤.
         2: exact {[ρ_lib := client_fl]}.
         2: exact lb'.
         done. }
    2: { rewrite LIVE2 LIVE1. set_solver. }
    2: { set_solver. }
    2: { set_solver. }
    2: { red. intros.
         red. 
         rewrite /update_mapping. rewrite map_imap_dom_eq.
         2: { intros. destruct decide; [| done].
              by apply elem_of_dom. }
         rewrite dom_gset_to_gmap.
         intros. 
         rewrite !dom_singleton.
         assert (gi = ρlg) as ->.
         { by destruct gi, ρlg. }
         set_solver. }
    { repeat split; rewrite ?LIVE2 ?LIVE1.
      1-3, 5-7: set_solver.
      intros. assert (ρ' = ρ_lib) as -> by set_solver.
      rewrite lookup_singleton. simpl. lia. }
    do 3 iModIntro. iIntros "ST FR FUELS".
    rewrite LIVE2 LIVE1.
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { Unshelve. 2: exact {[ ρ_cl; ρ_ext ]}. set_solver. } 
    simpl.    

    iApply fupd_wp.
    iPoseProof (init_client_inv with "ST") as "inv".
    iMod (fupd_mask_mono with "inv") as (?) "(#INV & LF & LM & LST & LFR & YST)".
    { set_solver. }
    iModIntro.

    wp_bind (lib_fun #())%E.
    (* iDestruct "FUELS" as "[MAP FUELS]".  *)
    iDestruct (has_fuels_equiv with "FUELS") as "[MAP FUELS]".
    iApply (lib_spec with "[] [LST YST LF LM FR MAP FUELS]").
    { iApply lib_PMP; [done| ]. iSplit; done. }
    {
      (* simpl. *)
      iDestruct (lib_premise with "LST LF LM") as "(LST & LF & LM)"; eauto.
      { apply lib_reset_premise. }
      rewrite has_fuels_equiv. simpl.
      iDestruct (partial_free_roles_are_sep with "FR") as "[FR FR']"; [set_solver| ].
      rewrite dom_singleton_L !big_sepM_singleton.
      iFrame.
      do 3 iExists _. iFrame "FR". iFrame. iSplitR.
      { iPureIntro. by rewrite dom_singleton_L. }
      iLeft.
      rewrite bi.sep_assoc. iSplitR.
      { iPureIntro. set_solver. }
      (* rewrite !map_fmap_singleton big_sepM_singleton. *)
      iExists _. iFrame. iPureIntro. rewrite /client_fl. lia. }
 
    iNext. iIntros "[LMAP LFR']". simpl.
    iDestruct "LMAP" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    assert (L = ∅) as -> by set_solver.
    iDestruct "MATCH" as "[[%?] | (_&[->->]&FUEL')]"; [set_solver| ]. clear LIBM.
                                      
    iAssert (has_fuels 0 {[ ρ_cl := 15 ]})%I with "[FUEL' MAP]" as "FUELS".
    { rewrite /has_fuels.
      rewrite !dom_singleton_L !big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }
    
    simpl. clear FS.
    rewrite (sub_0_id {[ ρ_cl := _ ]}).
    assert (fuels_ge ({[ ρ_cl := 15 ]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[? ?]%lookup_singleton_Some. lia. }

    pure_step FS. pure_step FS.
    
    wp_bind (_ <- _)%E.

    iApply wp_atomic.
    iInv Ns as ((lb, y)) "inv" "CLOS". rewrite {1}/client_inv_impl.
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".
    iAssert (⌜ y = 1 ⌝)%I as %->.
    { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V.
      apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. }
    iAssert (⌜ ls_tmap lb !! ρlg = Some ∅ ⌝)%I as %LIB_END.
    { iApply (frag_mapping_same with "[inv'] LM").
      rewrite /model_state_interp. iFrame.
      iDestruct "inv'" as (?) "(?&?&_)". iFrame.  }

    pose proof (live_roles_1 lb) as LIVE1'.
    (* rewrite !(decide_False, decide_True) in LIVE1'. -- TODO: how to do it in ssr?*)
    erewrite decide_False, decide_True in LIVE1'; eauto.
    2: { apply LM_map_empty_notlive. eauto. }
    
    pose proof (live_roles_0 lb) as LIVE0.
    
    iModIntro.
    iApply (wp_store_step_singlerole_keep with "[$] [L ST FUELS]").
    { set_solver. }
    (* { reflexivity. } *)
    6: { iFrame "L ST". iNext.
         iApply has_fuel_fuels. rewrite map_fmap_singleton. iFrame. }
    2: { by apply ct_y_step_1. }
    3: { rewrite LIVE1' LIVE0. set_solver. }
    { Unshelve. 2: exact 7. simpl. rewrite /client_fl. lia. }
    { lia. }
    { red. intros. simpl. red.
      intros ? [? MAP].
      apply (ls_mapping_tmap_corr (LM := lib_model)) in MAP as (? & TMAP' & ?).
      assert (ρlg = gi) as <- by (by destruct ρlg, gi).
      set_solver. }

    (* rewrite LIVE0. erewrite decide_False; [| set_solver]. *)
    iNext. iIntros "(L & ST & FUELS)".
    iMod (y_update_model _ _ 0 with "YST_AUTH YST") as "[YST_AUTH YST]".
    
    iMod ("CLOS" with "[YST_AUTH ST inv']") as "_".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iModIntro.

    iDestruct (has_fuel_fuels with "FUELS") as "FUELS".
    simpl. clear FS.
    rewrite (sub_0_id {[ ρ_cl := _ ]}).
    assert (fuels_ge ({[ ρ_cl := 7 ]}: gmap (fmrole client_model_impl) nat) 7) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    do 2 pure_step FS.

    iApply wp_atomic.
    iInv Ns as ((lb'', y)) "inv" "CLOS". rewrite {1}/client_inv_impl.
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".
    iAssert (⌜ y = 0 ⌝)%I as %->.
    { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V.
      apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. }

    (* Unshelve. 2: exact (⊤ ∖ ↑Ns).  *)
    iModIntro.
    
    iApply (wp_lift_pure_step_no_fork_remove_role {[ ρ_cl ]} ((lb'', 0): fmstate client_model_impl) _ _ _ _ _ _ _ (sub 3 <$> {[ρ_cl := 7]}) (iLM := client_model)); eauto.
    { solve_map_not_empty. }
    { set_solver. }
    { rewrite live_roles_0. set_solver. }
    { red. intros. red. intros.
      red in H0. specialize (H0 _ H1).
      rewrite dom_filter_comm. apply elem_of_filter. split; set_solver. }
    iFrame "PMP". do 3 iModIntro. iFrame.
    iSplitL "FUELS".
    { solve_fuels_S FS. }
    iIntros "ST FUELS".

    simpl. iApply wp_value'.
    iMod ("CLOS" with "[ST YST_AUTH inv']") as "_".
    { rewrite /client_inv_impl. iNext. iExists (_, _). iFrame. }
    iModIntro. iApply "POST".
    iDestruct (has_fuels_equiv with "FUELS") as "[MAP FUEL]".
    iApply partial_mapping_is_Proper; [| by iFrame].
    f_equiv. rewrite map_fmap_singleton dom_singleton_L.
    rewrite difference_diag_L.
    rewrite dom_filter_comm.
    by rewrite dom_singleton_L filter_singleton_not.
  Qed.
  
 
End ClientSpec.

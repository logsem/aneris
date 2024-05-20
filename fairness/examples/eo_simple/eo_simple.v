From iris.proofmode Require Import tactics.
From trillium.fairness Require Import resources.
From trillium.fairness.heap_lang Require Import notation heap_lang_defs wp_tacs sswp_logic ewp_model_logic.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair fairness fuel. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.heap_lang Require Export lang notation. 
From trillium.program_logic Require Import ewp. 

Close Scope Z_scope.


Section Even.
  
  (* TODO: move to ~= heap_lang_defs, remove duplicates *)
  Let PI
    (* `{hG: gen_heapGS loc val Σ} *)
    `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}
    (p: state heap_lang) := gen_heap_interp p.(heap). 


  Class EvenInterface := {
      evenM: FairModel;
      (* libEM: ExtModel libM (fmrole libM); *)
      (* lib_step_ex_dec :> forall st ρ, Decision (exists st', fmtrans libM st (Some ρ) st'); *)
      (* reset_lib := @ETs _ _ libEM; *)
      (* lib_reset_dom: forall ρ st, in_dom_rel (reset_lib ρ) st <-> ¬ role_enabled_model ρ st; *)
      (* lib_reset_cod: forall ρ st, in_cod_rel (reset_lib ρ) st -> role_enabled_model ρ st; *)
      even_strong_lr: FM_strong_lr evenM;

      (* evenGSPre: gFunctors -> Set; *)
      evenGS: gFunctors -> Set;
      even_msi `{!evenGS Σ}: fmstate evenM -> iProp Σ;
      even_pre `{evenGS Σ}: fmrole evenM -> iProp Σ;
      even_post `{evenGS Σ}: fmrole evenM -> iProp Σ;
      (* even_st0: fmstate evenM; *)
      (* even_init `{l0: evenGSPre Σ}: ⊢ ∀ ρ, |==> ∃ (l: evenGS Σ), even_msi lib_st0 (libGS0 := l) ∗ even_pre ρ (libGS0 := l); *)
      (* lib_post_dis `{l: libGS Σ}: ⊢ ∀ ρ st, lib_msi st (libGS0 := l) ∗ lib_post ρ (libGS0 := l) → ⌜ ¬ role_enabled_model ρ st ⌝; *)
      (* lib_reset `{l: libGS Σ}: *)
      (*   ⊢ ∀ st st' ρ, *)
      (*              lib_msi st (libGS0 := l) -∗ lib_post ρ (libGS0 := l) -∗ *)
      (*              ⌜ reset_lib ρ st st' ⌝ *)
      (*              ==∗ *)
      (*              lib_msi st' (libGS0 := l) ∗ lib_pre ρ (libGS0 := l); *)

      (* lib_step_restr (δ1 δ2: fmstate libM) := live_roles _ δ2 ⊆ live_roles _ δ1; *)
      even_step_restr (δ1 δ2: fmstate evenM) := live_roles _ δ2 ⊆ live_roles _ δ1;
      ewp'_even `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM} `{e: evenGS Σ} := ewp'
          (PI := PI)
          (MSI := even_msi (evenGS0 := e))
          (step_restr := even_step_restr);

      E__even: coPset;
      even_fun: val heap_lang;
      even_spec `{e: evenGS Σ} `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}
        (ρ: fmrole evenM):
      ⊢ (□ ∀ Φ,
             (even_pre ρ (evenGS0 := e)) -∗
              ▷ (∀ y, even_post ρ (evenGS0 := e) -∗ Φ y) -∗
              @ewp _ _ _ _ (ewp'_even (e := e)) NotStuck E__even ρ (even_fun #()) Φ);
      even_fun_nonval: heap_lang.to_val even_fun = None;
  }.  

End Even. 

Section IncrModel.
  (* Context `{cG: clientGS Σ} `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}.  *)
  (* Inductive incr_role := ρ__i.  *)
  Definition incr_role := unit.
  Definition ρ__i: incr_role := (). 
  
  Inductive incr_trans: nat -> option incr_role -> nat -> Prop :=
  | incr_trans_S n : incr_trans n (Some ρ__i) (S n)
  .
  
  Definition incr_state := nat. 
  
  Definition incr_lr (_: incr_state): gset incr_role :=
    {[ ρ__i ]}.
  
  Lemma incr_lr_spec: ∀ s ρ,
      (exists s', incr_trans s (Some ρ) s') <-> ρ ∈ incr_lr s.
  Proof.
    intros. rewrite /incr_lr elem_of_singleton. split.
    - intros [? STEP]. by inversion STEP.
    - intros ->. eexists. econstructor.
  Qed. 
  
  Definition incr_model_impl: FairModel.
  Proof.
    refine({|
              fmstate := incr_state;
              fmrole := incr_role;
              fmtrans := incr_trans;
              live_roles := incr_lr;
            |}).
    intros. eapply incr_lr_spec; eauto. 
  Defined.

  (* Lemma incr_live_roles s: live_roles incr_model_impl s = incr_lr s. *)
  (* Proof. done. Qed.  *)
  
  Definition G__incr := unit.
  
  (* TODO: replace LSI_True with the needed condition *)
  Definition incr_fl := 100.
  Definition incr_LSI (s: fmstate incr_model_impl)
    (tm: groups_map (M := incr_model_impl) (G := G__incr))
    (fm: gmap (fmrole incr_model_impl) nat) :=
    LSI_True s tm fm. 
  Definition incr_model: LiveModel G__incr incr_model_impl incr_LSI :=
    {| lm_fl (x: fmstate incr_model_impl) := incr_fl; |}.
  
  Instance LFP__incr: LMFairPre incr_model.
  Proof. Admitted.
  Definition FM__incr := LM_Fair (LF := LFP__incr). 

  Section Proofs.
    Context {Σ: gFunctors} {fG: fairnessGS incr_model Σ}.
    Context `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}. 
  (* Context `{cG: clientGS Σ} `.  *)

    (* TODO: move to ~= heap_lang_defs, remove duplicates *)
    Let PI
    (* `{hG: gen_heapGS loc val Σ} *)
    `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}
    (p: state heap_lang) := gen_heap_interp p.(heap). 

    Let lr (δ: fmstate FM__incr) := dom (ls_tmap δ). 
    Let step_restr st1 st2 := lr st2 ⊆ lr st1. 
    (* Let PI (p: state heap_lang) := gen_heap_interp p.(heap).  *)
    Let msi: fmstate FM__incr -> iProp Σ := model_state_interp (LM := incr_model).
  
    Let ewp'_instance_helper := ewp' (PI := PI) (MSI := msi) (step_restr := step_restr).
    Existing Instance ewp'_instance_helper. 
  
  Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

  Lemma incr_impl_lift:
  ∀ (δ1 δ2: fmstate FM__incr) (g0 : G__incr) (R2 : gset
                                                     (fmrole incr_model_impl)),
    locale_trans δ1 g0 δ2 (LM := incr_model) → ls_tmap δ2 = <[g0:=R2]> (ls_tmap δ1) → lr δ2 ⊆ lr δ1.
  Proof using.
    clear dependent Σ. 
    intros ???? STEP TM.
    apply locale_trans_dom in STEP.
    rewrite /lr. rewrite TM dom_insert_L. set_solver.
  Qed. 



  From trillium.fairness Require Import model_plug.
  (* TODO: why does it require specifying the role? *)
  Ltac pure_step ρ FS indep :=
    try rewrite sub_comp;
    (* iApply (sswp_MU_cwp with "[FUELS] [-]").  *)
    iApply (sswp_MU_ewp _ ρ);
    iApply sswp_pure_step; [done| ]; simpl;
    iNext;
    iApply (LMU_mono with "[-FUELS]");
    [| iApply local_rule_LMU;
       [iApply fuel_keep_step_local_rule; apply incr_impl_lift | 
        iApply bi.sep_assoc; iSplit; [| solve_fuels_S FS]; iPureIntro; split; [| apply indep]; set_solver]];
    iIntros "FUELS".

From trillium.fairness.lm_rules Require Import resources_updates.

  Lemma fuel_reorder_preserves_incr_LSI:
    @fuel_reorder_preserves_LSI G__incr _ _
      (incr_model_impl) LSI_True. 
  Proof.
    done. 
    (* red. rewrite /incr_LSI. intros * EQ1 EQ2 EQ3. *)
    (* intros ? LSI1 IN2. rewrite <- EQ2. auto.  *)
  Qed.

  Lemma incr_LSI_fuel_independent:
    @LSI_fuel_independent G__incr _ _ 
      (incr_model_impl) LSI_True.
  Proof.
    done. 
    (* red. rewrite /incr_LSI. intros. *)
    (* set_solver. *)
  Qed.

  Lemma incr_model_step_preserves_LSI st1 st2 ρ fm1 fm2:
    model_step_preserves_LSI st1 ρ st2 fm1 fm2 (LSI := incr_LSI).
  Proof.
    done.
  Qed.

  Definition incr_loop: val heap_lang :=
    rec: "incr_loop" "l" (* "n" *) :=
      (* (if: CAS "l" "n" ("n"+#1) *)
      (*  then "incr_loop" "l" ("n" + #2) *)
      (*  else "incr_loop" "l" "n"). *)
      FAA "l" #1%nat ;;
      "incr_loop" "l"
  .

  Definition cur_n (n: nat): iProp Σ := partial_model_is n. 

  (* TODO: move, try to get rid of this version *)
  Lemma sub_comp' `{Countable K} (fs: gmap K nat) (d1 d2: nat):
    (sub d1 <$> (sub d2 <$> fs)) = sub (d1 + d2) <$> fs.
  Proof.
    rewrite -map_fmap_compose. apply sub_comp.  
  Qed.

    Let fuel_sub := 2. 

    Lemma incr_loop_spec (g__incr: fmrole FM__incr) (l: loc) E__incr ι:
      (* (∀ v δ, Φ v -∗ MSI__lib δ -∗ ⌜ ¬ role_enabled_model ρlg δ ⌝) -∗ *)
      (* client_inv -∗ *)
      has_fuels g__incr (sub fuel_sub <$> {[ ρ__i := incr_fl ]}) -∗
      partial_free_roles_are ∅ -∗                
      (* EWP (lib_fun #()) @ s ; g__cl ; E {{ v, Φ v }}. *)
      (* y_frag_model_is 1 -∗       *)
      (* @ewp _ _ _ _ (ewp'_lib (l := libGSΣ)) s E__lib ρlg e Φ -∗ *)
      (* even_pre ρ__e (evenGS0 := evenGSΣ) -∗  *)
      (□ |={E__incr, E__incr ∖ ↑ι}=> ▷ ∃ (n: nat), l ↦ #n ∗ cur_n n ∗ (l ↦ #(n + 1%nat) -∗ cur_n (n + 1) ={E__incr ∖ ↑ι, E__incr}=∗ True)) -∗
      EWP (incr_loop #l) @ NotStuck ; g__incr ; E__incr
        {{ v, False }}.
    Proof. 
      iLöb as "IH". 
      iIntros "FUELS FREE #EXT_INV". rewrite {2}/incr_loop.

      rewrite (sub_0_id {[ _ := _ ]}).
      assert (fuels_ge ({[ρ__i := incr_fl]}: gmap (fmrole incr_model_impl) nat) 10) as FS.
      { red. intros ??[<- <-]%lookup_singleton_Some. rewrite /incr_fl. lia. }

      (* Unset Printing Notations. *)
      repeat rewrite sub_comp'. 
      pure_step g__incr FS incr_LSI_fuel_independent.

      ewp_bind (FAA _ _)%E.
      iApply sswp_MU_ewp_fupd.
      iPoseProof "EXT_INV" as "-#E". 
      iMod "E" as (n) "(>N & >CUR & CLOS)". iModIntro.
      iApply (wp_faa with "[$]"). iNext. iIntros "N".
      iApply (LMU_mono with "[-FUELS FREE CUR]").
      2: { iApply local_rule_LMU.
           { iApply model_step_local_rule. apply incr_impl_lift. }
           iFrame. iPureIntro. simpl. rewrite /incr_lr. 
           do 6 (try split).
           5: by apply incr_model_step_preserves_LSI. 
           Unshelve. 
           6: exact ∅.
           5: exact ({[ ρ__i := incr_fl ]}).
           1-3: set_solver. 
           red. simpl. rewrite /incr_lr. 
           rewrite !map_fmap_singleton !dom_singleton_L.
           do 5 (try split).
           all: try by set_solver.
           - intros ?%elem_of_singleton. rewrite lookup_insert. simpl. lia.
           - intros ?? [->%elem_of_singleton ?]%elem_of_intersection. done. }
      iIntros "(FUELS & ST & FREE)".
      iDestruct (partial_free_roles_are_Proper with "FREE") as "FREE". 
      { rewrite union_empty_r. rewrite subseteq_empty_difference_L; [reflexivity|].
        done. }

      rewrite -(Nat.add_1_r n). iMod ("CLOS" with "[$][$]") as "_".
      iModIntro.

      iApply ewp_value.

      ewp_bind (Rec _ _ _)%E.
      clear FS. 
      rewrite (sub_0_id {[ _ := _ ]}).
      assert (fuels_ge ({[ρ__i := incr_fl]}: gmap (fmrole incr_model_impl) nat) 10) as FS.
      { red. intros ??[<- <-]%lookup_singleton_Some. rewrite /incr_fl. lia. }
      rewrite /incr_fl in FS. rewrite /incr_fl. 

      pure_step g__incr FS incr_LSI_fuel_independent.

      iApply ewp_value.

      repeat rewrite sub_comp'.
      pure_step g__incr FS incr_LSI_fuel_independent.
 
      iApply ("IH" with "[$] [$] [$]").
    Qed. 
          
  End Proofs. 
    
End IncrModel.
  



Section ClientDefs.

  Context {lib: EvenInterface}. 

  Let even_st := fmstate evenM.
  Let even_role := fmrole evenM.

  Definition client_state: Type := even_st * nat.

  (* Inductive y_role := ρ__y. *)
  Definition y_role := unit.
  Let ρ__y: y_role := (). 
  Definition client_role: Type := even_role + y_role.

  Context {ρ__e: fmrole evenM}. 

  Definition ρ__cl: client_role := inr ρ__y.
  Definition ρ__lift: client_role := inl ρ__e.

  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_even_step lb1 lb2 (EVEN_STEP: fmtrans _ lb1 (Some ρ__e) lb2):
    client_trans (lb1, 1) (Some ρ__lift) (lb2, 1)
  | ct_y_step_1 (lb: fmstate evenM)
      (EVEN_STOP: ¬ role_enabled_model (ρ__e: fmrole evenM) lb)
    :
    client_trans (lb, 1) (Some ρ__cl) (lb, 0)
  .

  (* Instance y_EqDec: EqDecision y_role. *)
  (* Proof. red. intros [] []. by left. Defined.   *)

  (* Instance client_role_EqDec: EqDecision client_role. *)
  (* Proof. *)
  (*   eapply sum_eq_dec.  *)
  (*   pose proof (fmrole_eqdec evenM).  *)
  (*   apply _.  *)

  (* Instance y_cnt: Countable y_role. *)
  (* Proof.  *)

  (* Instance cl_cnt: Countable client_role. *)
  (* Proof.  *)
  (*   eapply sum_countable.  *)


  Definition client_lr (st: client_state): gset (client_role) :=
    let '(lb, y) := st in
    if (decide (y = 1)) then
      {[ if (decide (role_enabled_model ρ__e lb)) then ρ__lift else ρ__cl ]}
    else ∅. 

  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role),
      (exists s', client_trans s (Some ρ) s') <-> ρ ∈ client_lr s.
  Proof.
    intros [lb y] ?. rewrite /client_lr.
    destruct (decide (y = 1)).
    2: { split; [| set_solver]. intros [? STEP]. inversion STEP; lia. }
    subst. rewrite elem_of_singleton.
    split.
    - intros [? STEP]. inversion STEP; subst; auto.
      + rewrite decide_True; auto. apply even_strong_lr. eauto.
      + rewrite decide_False; auto.
    - destruct decide; intros ->.
      + red in r. apply even_strong_lr in r as [??]. 
        eexists. econstructor. eauto.
      + eexists. econstructor. eauto.
  Qed.

  Instance cs_eqdec: EqDecision client_state.
  Proof.
    pose proof (fmstate_eqdec evenM). 
    apply prod_eq_dec.
  Defined. 

  Definition client_model_impl: FairModel.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    intros. apply client_lr_spec. eauto.
  Defined. 

  Definition client_LSI 
    (s: fmstate client_model_impl)
    (tm: groups_map (M := client_model_impl) (G := locale heap_lang))
    (fm: gmap (fmrole client_model_impl) nat) :=
    (* forall gi, (exists ρi, ls_mapping s.1 !! ρi = Some gi) -> inl $ inl gi ∈ mapped_roles tm. *)
    LSI_True s tm fm. 
    
  Definition client_fl := 15. 
  Definition client_model: LiveModel (locale heap_lang) client_model_impl client_LSI :=
    {| lm_fl _ := client_fl; |}.

  Class clientGS Σ := ClientGS {
    (* cl_pre_inG :> clientPreGS Σ;     *)
    cl_y_st :> inG Σ (authUR (optionR (exclR natO)));
    cl_y_st_name : gname;
    cl_LMΣ :> fairnessGS client_model Σ;
    (* cl_tracker_name : gname; *)
    (* cl_set_pair_name: gname;                           *)
    evenGSΣ :> evenGS Σ;
  }.
  
  Definition client: val heap_lang :=
    λ: <>, even_fun #().

  (* Let ST := fmstate M__cl. *)
  (* Let R := fmrole M__cl. *)

  (* Let STl := fmstate libM. *)
  (* Let Rl := fmrole libM.  *)

  Section Proofs.
    Context `{cG: clientGS Σ} `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}. 

    Definition y_auth_model_is (y: nat): iProp Σ :=
      own cl_y_st_name (● Excl' y).

    Definition y_frag_model_is (y: nat): iProp Σ :=
      own cl_y_st_name (◯ Excl' y).

    (* Let lg := @libGSΣ _ _ _ cG. *)

    Definition MSI__even (lb: fmstate evenM) := even_msi lb (evenGS0 := evenGSΣ). 
    Definition MSI__cl := model_state_interp (LM := client_model) (fG := cl_LMΣ).

    Definition client_inv_impl (st: fmstate client_model_impl) : iProp Σ :=
      let (lb, y) := st in
      partial_model_is st (LM := client_model) ∗
      y_auth_model_is y ∗
      MSI__even lb
    .

    Definition Ns := nroot .@ "client".
    
    Definition client_inv: iProp Σ :=
      inv Ns (∃ st, client_inv_impl st).

    Instance LFP__cl: LMFairPre client_model.
    Proof. Admitted.
    Definition FM__cl := LM_Fair (LF := LFP__cl). 
    
    
    Let lr (δ: fmstate FM__cl) := dom (ls_tmap δ). 
    Let step_restr st1 st2 := lr st2 ⊆ lr st1. 
    Let PI (p: state heap_lang) := gen_heap_interp p.(heap). 
    Let msi: fmstate FM__cl -> iProp Σ := model_state_interp (LM := client_model).

    Let ewp'_instance_helper := ewp' (PI := PI) (MSI := msi) (step_restr := step_restr).  
    Existing Instance ewp'_instance_helper. 


  Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

  Lemma lift_even_spec s (g__cl: fmrole FM__cl)
    E__lib Φ (f: nat) e
    (NV: to_val e = None)
    (DIS: ↑Ns ⊆ E__lib)
    (FUEL_BOUND: f ≤ client_fl):
    ⊢
      (∀ v δ, Φ v -∗ MSI__even δ -∗ ⌜ ¬ role_enabled_model ρ__e δ ⌝) -∗
      client_inv -∗
      has_fuels g__cl {[ ρ__lift := f ]} -∗ 
      partial_free_roles_are {[ ρ__cl ]} -∗
      y_frag_model_is 1 -∗      
      @ewp _ _ _ _ (ewp'_even (e := evenGSΣ)) s E__lib ρ__e e Φ -∗
      EWP e @ s ; g__cl ; E__lib
        {{ v, Φ v ∗ has_fuels g__cl {[ ρ__cl := f ]} ∗ partial_free_roles_are {[ ρ__lift ]} ∗ y_frag_model_is 1 }}.
  Proof.
    iIntros "POST_DIS #INV_CL FUELS FREE Y1 EWP_LIB".
    iLöb as "IH" forall (e NV).
    rewrite (ewp_unfold _ _ _ g__cl) /ewp_pre. simpl. rewrite NV. 
    iIntros (σ1 δ__cl) "PI MSI_cl".

    iInv "INV_CL" as ([lb y]) "INV" "CLOS".
    rewrite /client_inv_impl. iDestruct "INV" as "(>ST & >Y_AUTH & LIB_MSI)". 
    
    rewrite ewp_unfold /ewp_pre. simpl. rewrite NV.




    Lemma client_spec (g__cl: fmrole FM__cl) f:
      (* (∀ v δ, Φ v -∗ MSI__lib δ -∗ ⌜ ¬ role_enabled_model ρlg δ ⌝) -∗ *)
      client_inv -∗
      has_fuels g__cl {[ ρ__lift := f ]} -∗ 
      partial_free_roles_are {[ ρ__cl ]} -∗
      (* EWP (lib_fun #()) @ s ; g__cl ; E {{ v, Φ v }}. *)
      y_frag_model_is 1 -∗      
      (* @ewp _ _ _ _ (ewp'_lib (l := libGSΣ)) s E__lib ρlg e Φ -∗ *)
      even_pre ρ__e (evenGS0 := evenGSΣ) -∗ 
      EWP (client #()) @ NotStuck ; g__cl ; E__even
        {{ v, has_fuels g__cl ∅ ∗ partial_free_roles_are {[ ρ__lift; ρ__cl ]} ∗ y_frag_model_is 0 }}.
    Proof.
      iIntros "INV FUELS FREE Y_FRAG EVEN_PRE". 


  End Proof. 

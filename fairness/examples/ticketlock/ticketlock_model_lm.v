From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fuel lm_fair fairness_finiteness lm_fairness_preservation. 
From trillium.fairness.examples.ticketlock Require Import fair_lock ticketlock_model fair_lock_lm lm_restr.
From stdpp Require Import base.
From trillium.fairness.ext_models Require Import ext_models. 
From trillium.fairness Require Import comp_utils.

Section TlLM.
  Let M := tl_fair_model.
  Let G := @SG M.
  Let R := fmrole tl_fair_model.
  
  Context {n_roles: nat}.
  Let roles: gset R := dom $ snd $ tl_init_st' n_roles. 
  Definition tl_gs: gset G := set_map asG roles.

  (* TODO: prove that size (set_map f S) = size S *)
  Lemma tl_gs_size: size tl_gs = n_roles.
  Proof.
    rewrite /tl_gs.
  Admitted.
  
  Definition LSI_Tl (st: fmstate M) (tm: groups_map) (fm: @fuel_map M) :=
    (* LSI_groups_fixed gs st tm fm /\ *) (* <- implied by last condition *)
    map_Forall (fun '(asG ρ) Rs => Rs ⊆ {[ ρ ]}) tm /\
    (forall ρ: fmrole M, ¬ is_unused ρ st <-> asG ρ ∈ dom tm) /\
    dom tm = tl_gs. 

  Definition tl_fl := 100. 
  
  Definition tl_model: LiveModel G M LSI_Tl :=
    {| lm_fl _ := tl_fl; |}.

  Lemma dom_tmap_tl_fixed (δ: lm_ls tl_model):
    dom (ls_tmap δ) = tl_gs.
  Proof. apply δ. Qed. 

  Lemma tl_ls_map_restr (δ: lm_ls tl_model): ls_map_restr (ls_mapping δ).
  Proof.
    red. intros ? [] (?&TM&?)%ls_mapping_tmap_corr.
    apply (ls_inv δ) in TM. set_solver.
  Qed. 

  Lemma tl_unused_not_dom: ∀ ρ (δ : lm_ls tl_model),
      fair_lock.is_unused ρ (ls_under δ) (FairLockPredicates := tl_FLP) ↔ asG ρ ∉ dom (ls_tmap δ).
  Proof.
    intros. simpl. 
    pose proof (proj1 (proj2 (ls_inv δ)) ρ).
    tauto.
  Qed. 
      
  Instance tl_step_dec s1 ρ s2: Decision (fmtrans M s1 (Some ρ) s2).
  Proof.
    Local Ltac nostep := right; intros S; inversion S; subst; set_solver.
    destruct s1 as [o1 t1 rm1 wf1], s2 as [o2 t2 rm2 wf2].
    destruct (rm1 !! ρ) as [[s e]| ] eqn:RR.
    2: { right. intros STEP%live_spec_holds. rewrite /tl_live_roles in STEP.
         simpl in STEP. apply elem_of_dom in STEP as [? X%map_filter_lookup_Some].
         rewrite RR in X. set_solver. }
    destruct e.
    2: { right. intros STEP%live_spec_holds. rewrite /tl_live_roles in STEP.
         simpl in STEP. apply elem_of_dom in STEP as [? X%map_filter_lookup_Some].
         rewrite RR in X. set_solver. }
    destruct s as [| k]. 
    { destruct (decide (
                      o2 = o1 /\ t2 = t1 + 1 /\ 
                      let next_en := if decide (o1 = t1) then false else true in
                      rm2 = <[ρ := (tl_U t1, next_en)]> rm1)) as [T| ?].
      - destruct T as (->&->&->).
        left. by constructor.
      - right; intros S; inversion S; subst. 
        + set_solver.
        + by rewrite RR in R0. 
        + by rewrite RR in R0. }
    destruct (decide (o1 ≠ k /\ o2 = o1 /\ t2 = t1 /\ rm2 = rm1)) as [T| ?].
    { inversion T as (?&->&->&->). left. by econstructor. }
    destruct (decide (k = o1 /\
                        let st' := (o1 + 1, t1, <[ρ := (tl_L, false)]> rm1) in
                        let st'' := advance_next st' in
                        (o2, t2, rm2) = st'')) as [T |]. 
    { destruct T as [-> ST2].
      left. simpl. red. simpl.
      rewrite ST2. by econstructor. }
    right; intros S. inversion S; subst. 
    all: rewrite RR in R0; inversion R0; subst. 
    + destruct n. done.
    + destruct n0. done. 
  Qed.

(*   (* TODO: move, upstream *) *)
(*   Lemma dom_set_to_map: *)
(* (* B is element type, C is container, K is key, A is value, M is map *) *)
(* ∀ {B C : Type} `{Elements B C} {K A M : Type} `{Insert K A M} `{Empty M} *)
(*   `{Dom M C}, *)
(*   forall f X, dom (set_to_map f X) = set_map (fst ∘ f) X. *)
  Lemma dom_set_to_map_gset_gmap {B K A: Type} `{Countable B} `{Countable K}
    (f: B -> K * A)
    (X: gset B): 
    dom ((set_to_map f X): gmap K A) = set_map (fst ∘ f) X.
  Proof.
    simpl. rewrite /set_to_map.
    rewrite dom_list_to_map_L. set_solver.
  Qed. 

  Instance tl_inh0: Inhabited (lm_ls tl_model).
  Proof. 
    apply populate. unshelve refine {|
        (* ls_under := (tl_init_st', fs_U): fmstate client_model_impl; *)
        ls_fuel := gset_to_gmap tl_fl roles;
        ls_tmap := set_to_map (fun ρ => (asG ρ, {[ ρ ]}: gset R)) roles;
      |}.
    - esplit. apply (tl_init_st'_wf n_roles).
    - simpl. rewrite /tl_live_roles. simpl.
      etrans; [apply dom_filter_subseteq| ].
      rewrite /roles. simpl.
      by rewrite !dom_gset_to_gmap.
    - intros.
      rewrite !dom_gset_to_gmap.
      etrans.
      2: { do 2 (apply exist_proper; intros).
           rewrite lookup_set_to_map.
           2: { simpl. congruence. }
           apply Morphisms_Prop.and_iff_morphism; reflexivity. }
      simpl. erewrite ex_det_iff2.
      2: { intros ??  [(?&?&[=]) ?]. subst.
           apply elem_of_singleton in H3. subst. split; reflexivity. }
      set_solver. 
    - red. intros *. rewrite !lookup_set_to_map.
      2, 3: simpl; congruence.
      intros ? (?&?&[=]) (?&?&[=]). subst. set_solver.
    - simpl. split; [| split]. 
      + rewrite map_Forall_lookup. 
        intros [?] ? L. 
        simpl. eapply @lookup_set_to_map in L.
        2, 3: apply _.
        2: set_solver.
        destruct L as (?&?&[=]). by subst.
      + intros. rewrite /is_unused /roles. simpl.
        rewrite !dom_gset_to_gmap !dom_set_to_map_gset_gmap.
        rewrite elem_of_map. simpl.
        rewrite ex_det_iff. 
        2: { intros ? [[=] ?]. subst. reflexivity. }
        tauto. 
      + rewrite dom_set_to_map_gset_gmap. set_solver.
  Defined.

  Let encode_rs := fun rs => match rs with | tl_U k => S k | _ => 0 end. 

  Instance tl_role_stage_Cnt: Countable tl_role_stage. 
  Proof using.
    eapply inj_countable' with
      (f := encode_rs)
      (g := fun i => match i with | 0 => tl_L | S i => tl_U i end).
    by intros [].
  Qed.

  (* (* TODO: move *) *)
  Lemma Forall_dec': ∀ {A : Type} (P : A → Prop) (l: list A)
                       `{EqDecision A},
    (∀ x, x ∈ l -> Decision (P x)) → Decision (Forall P l).
  Proof.
    intros.
    eapply Decision_iff_impl; [symmetry; apply Forall_lookup| ].
    eapply Decision_iff_impl with
      (P := ∀ i x, l !! i = Some x → x ∈ l -> P x).
    { setoid_rewrite elem_of_list_lookup. set_solver. }
    eapply Decision_iff_impl; [apply Forall_lookup| ].
    apply Forall_dec. intros.
    destruct (decide (x ∈ l)).
    2: { left. tauto. }
    specialize (X _ e). solve_decision.
  Qed.

  (* (* TODO: move *) *)
  (* Lemma remove_is_Some: ∀ [A : Type] (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) *)
  (*                    (l : list A) (d : A) x, *)
  (*     (remove d l) !! i = Some x <-> l !! *)

  (* Lemma bool_forall_helper {P: bool -> Prop}: *)
  (*   (forall b: bool, (P b) -> b) <->  *)

  (* TODO: move *)
  Lemma forall_prod_helper' {A B: Type} (P: A * B -> Prop):
    (forall ab, P ab) <-> (forall a b, P (a, b)). 
  Proof.
    split; [by eauto|].
    intros PP [??]. eauto. 
  Qed.  

  Instance tl_state_wf_dec:
    forall st', Decision (tl_state_wf st').
  Proof.
    intros [[o t] rm]. rewrite /tl_state_wf.    
    repeat apply and_dec; try solve_decision.
    - set tks := (set_map (encode_rs ∘ fst) (map_img rm: gset (tl_role_stage * bool)): gset nat).
      eapply Decision_iff_impl with (P := tks ∖ {[ 0 ]} = set_seq (S o) (t - o)).
      2: solve_decision.
      subst tks. rewrite set_eq. 
      setoid_rewrite elem_of_difference. setoid_rewrite not_elem_of_singleton. 
      setoid_rewrite elem_of_map. setoid_rewrite elem_of_map_img. setoid_rewrite elem_of_set_seq.
      split.
      + intros DOM k. specialize (DOM (S k)). split. 
        * intros KK. apply proj2 in DOM. specialize_full DOM; [lia| ].
          destruct DOM as [([rs ?]&ENC&[??]) ?].
          simpl in ENC. destruct rs; simpl in ENC; [lia| ].
          inversion ENC. subst. eauto.
        * intros (?&?&RR). apply proj1 in DOM. specialize_full DOM.
          { split; [| done]. eexists. split; eauto. done. }
          lia.
      + intros DOM k. specialize (DOM (k - 1)). split.
        * intros [([rs ?]&->&[??]) ?]. destruct rs; simpl in *; [done| ].
          apply proj2 in DOM. specialize_full DOM.
          { rewrite PeanoNat.Nat.sub_0_r. eauto. }
          lia.
        * intros LT. destruct k; [lia| ].
          apply proj1 in DOM. specialize (DOM ltac:(lia)) as (?&?&?).
          split; [| lia]. eexists. split; eauto.
          simpl. lia.
    - eapply Decision_iff_impl with
        (P := map_Forall (fun ρ '(rs, e) => e = false -> match rs with | tl_U k => k = o | tl_L => True end) rm).
      2: { apply map_Forall_dec. intros ? [rs ?].
           apply impl_dec; [solve_decision| ].
           destruct rs; solve_decision. }
      rewrite map_Forall_lookup.
      apply forall_proper. intros ρ.
      destruct (rm !! ρ) as [[rs e] |] eqn:RR; rewrite RR. 
      2: { set_solver. }
      split.
      * intros O ? [=]; subst.
        specialize_full O; [reflexivity| ]. 
        simpl in O. lia.
      * intros O [??] [=] ->; subst.
        destruct t0; [done| ]. 
        specialize_full O; [reflexivity| ].
        done.
    - set check := fun '(ρ1, ρ2) =>
                     let r1 := fst $ default (tl_L, false) (rm !! ρ1) in
                     let r2 := fst $ default (tl_L, false) (rm !! ρ2) in
                     r1 ≠ r2 \/ (r1 = r2 /\ (r1 = tl_L  \/ ρ1 = ρ2)). 
      set pairs := ρ1 ← elements (dom rm); ρ2 ← elements (dom rm); mret (ρ1, ρ2). 
      apply Decision_iff_impl with (P := Forall check pairs).
      2: { solve_decision. }
      rewrite Forall_forall. subst pairs.
      setoid_rewrite <- elem_of_list_In. 
      repeat setoid_rewrite elem_of_list_bind.
      setoid_rewrite elem_of_list_ret. simpl.
      rewrite forall_prod_helper'.
      apply forall_proper. intros ρ1. apply forall_proper. intros ρ2. 
      rewrite ex_det_iff.
      2: { intros ? [(?&[=]&?) ?]. subst. reflexivity. } 
      rewrite ex_det_iff.
      2: { intros ? [[=] ?]. subst. reflexivity. }
      rewrite !elem_of_elements !elem_of_dom.
      destruct (rm !! ρ1) as [[rs1 ?]| ] eqn:R1, (rm !! ρ2) as [[rs2 ?]| ] eqn:R2; simpl.
      2-4: rewrite -!not_eq_None_Some; set_solver.
      rewrite !R1 !R2. simpl.
      destruct (decide (rs1 = rs2)).
      2: { set_solver. }
      subst. destruct rs2; simpl; set_solver. 
  Qed.          

  (* TODO: move, rename another *)
  Lemma ex_and_comm_r {T : Type} (A : Prop) (B : T → Prop):
    (∃ t, B t /\ A) ↔ (∃ t : T, B t) /\ A.
  Proof. set_solver. Qed. 

  (* TODO: move *)
  Lemma dec_dne `{Decision P}:
    P <-> ¬ ¬ P.
  Proof. tauto. Qed. 

  Lemma tl_model_impl_step_fin (s1 : fmstate M):
    (* {nexts: list tl_st | forall s2 oρ, tl_trans s1 oρ s2 -> s2 ∈ nexts}. *)
    next_states s1. 
  Proof.
    destruct s1 as [o t rm wf] eqn:S.
    set nexts' :=
      o' ← [o; o + 1];
      t' ← [t; t + 1];
      ρ' ← elements (dom rm);
      s' ← [tl_U t; tl_L];
      e' ← [true; false];
      let rm' := <[ ρ' := (s', e') ]> rm in
      let st' := ((o', t'), rm') in
      [st'; advance_next st']. 
    set nexts := 
      (s1 ::
      st' ← nexts';
      match (tl_state_wf_dec st') with
      | left wf' => [enhance_tl_st' st' wf']
      | right _ => []
      end).
    exists nexts. intros [o2 t2 rm2 wf2] * STEP. rewrite /nexts. 
    apply elem_of_cons. repeat setoid_rewrite elem_of_list_bind.
    repeat setoid_rewrite elem_of_elements.
    rewrite ex_det_iff.
    2: { intros [[]] [IN ?]. destruct tl_state_wf_dec.
         2: { edestruct @not_elem_of_nil. apply IN. }
         apply elem_of_list_singleton in IN.
         simpl in IN. inversion IN. subst. reflexivity. }
    simpl. destruct tl_state_wf_dec.
    2: { destruct n. eauto. }
    rewrite elem_of_list_singleton.
    rewrite /nexts'. repeat setoid_rewrite elem_of_list_bind.
    repeat setoid_rewrite <- ex_and_comm_r.
    eapply Morphisms_Prop.or_iff_morphism; [reflexivity| ..].
    { rewrite and_comm. apply iff_and_impl_helper. intros _.
      f_equal. apply wf_PI. }
    setoid_rewrite elem_of_elements.
    repeat setoid_rewrite elem_of_cons. 
    inversion STEP; subst.
    2: { left. f_equal. apply wf_PI. }
    { right. repeat eexists.
      { left. reflexivity. }
      all: try tauto. 
      { destruct next_en0; tauto. }
      eapply elem_of_dom; eauto. }
    right. repeat eexists.
    { right. left. reflexivity. }
    all: try tauto.
    eapply elem_of_dom; eauto.
  Qed.

  Global Instance LSI_Tl_dec: ∀ (a : M) (b : gmap G (gset (fmrole M))) (c : gmap (fmrole M) nat),
      Decision (LSI_Tl a b c).
  Proof.
    intros. rewrite /LSI_Tl. repeat apply and_dec; try solve_decision.
    - eapply @map_Forall_dec.
      { apply _. }
      intros [?] ?. solve_decision.
    - rewrite /is_unused.
      apply Decision_iff_impl with
        (P := set_map asG (dom $ role_map a) = dom b).
      2: solve_decision.
      rewrite set_eq.
      transitivity (∀ (ρ: fmrole M), (asG ρ: G) ∈ (set_map asG (dom (role_map a)): gset G) ↔ (asG ρ: G) ∈ (dom b: gset G)).
      { split; intros ?; [intros ? | intros [?]]; eauto. }
      apply forall_proper. intros. rewrite elem_of_map ex_det_iff.
      2: { intros ? [[=]?]. subst. reflexivity. }
      tauto. 
  Qed. 

  Instance tl_lm_dec_ex_step:
    ∀ τ δ1, Decision (∃ δ2, locale_trans δ1 τ δ2 (LM := tl_model)).
  Proof. 
    intros.
    pose proof (tl_model_impl_step_fin (ls_under δ1)) as [nexts NEXTS]. 
    apply locale_trans_ex_dec_fin with (steps := nexts).
    { intros. apply elem_of_list_In. eauto. }
    intros ??? STEP. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact tl_model. 
    +
      assert (dom (rearrange_roles_map (ls_tmap δ2) (dom (ls_tmap δ0)) τ0) = tl_gs) as DOM'.
      { rewrite /rearrange_roles_map.
        rewrite dom_insert_L.
        erewrite dom_domain_restrict_union_l.
        2: { rewrite subseteq_union_1; [reflexivity| ].
             by rewrite !dom_tmap_tl_fixed. }
        rewrite dom_tmap_tl_fixed.
        apply locale_trans_dom in STEP.
        rewrite dom_tmap_tl_fixed in STEP. set_solver. }

      red.
      split; [| split]; [..| done].
      2: { intros. rewrite DOM'.
           rewrite -(dom_tmap_tl_fixed δ2). apply δ2. }
      rewrite map_Forall_lookup. intros [ρ] Rρ TM.
      apply elem_of_subseteq. intros ρ' IN.
      apply elem_of_singleton.
      (* rewrite /rearrange_roles_map in TM.  *)
      
      forward eapply ls_mapping_tmap_corr_impl as MIM. 
      { eapply (rrm_tmap_disj (ls_tmap δ2) (dom (ls_tmap δ0)) τ0). apply δ2. }
      
      specialize (MIM ρ' (asG ρ)). apply proj2 in MIM. specialize_full MIM; [eauto| ].
      rewrite rrm_mapping in MIM; [| apply δ2].
      rewrite lookup_fmap in MIM.
      destruct (ls_mapping_impl (ls_tmap δ2) !! ρ') eqn:MAP; [| done].
      simpl in MIM. rewrite decide_True in MIM.
      2: { rewrite dom_tmap_tl_fixed -(dom_tmap_tl_fixed δ2).
           apply ls_mapping_tmap_corr in MAP as (?&?&?). 
           eapply elem_of_dom; eauto. }
      inversion MIM. subst.
      apply tl_ls_map_restr in MAP. congruence.
  Qed. 

  Global Instance TlLF: lm_fair.LMFairPre tl_model.
  esplit; by apply _.
  Qed. 
  
  Section TlFL.

    Let FLP_Tl := @FLP_LMF _ tl_FLP _ _ TlLF. 

    Section ImplFunctions.
      Context (g: G) (δ: lm_ls tl_model). 
      
      (* Let ρ := let '(asG ρ) := g in ρ.  *)

      Local Definition lm_ls_prop (new_st: fmstate M) (δ': lm_ls tl_model) :=
          let '(asG ρ) := g in
          ls_under δ' = new_st /\
          ls_tmap δ' = <[ asG (ρ: fmrole M) := {[ ρ ]} ]> (ls_tmap δ) /\
          ls_fuel δ' = <[ ρ := tl_fl ]> (ls_fuel δ).

      Section ExtTrans.
      Let ρ := match g with | asG ρ => ρ end.
      Context (new_st: fmstate M). 
      Context (TM: ls_tmap δ !! g = Some ∅).
      Context (DOM_RM: dom (role_map new_st) = {[ ρ ]} ∪ dom (role_map $ ls_under δ)).
      Context (LIVE': live_roles M new_st ⊆ dom (<[ρ:=tl_fl]> (ls_fuel δ))). 

      Lemma ext_trans_impl: {δ': lm_ls tl_model | lm_ls_prop new_st δ'}.
      Proof.
        rewrite /lm_ls_prop.  
        destruct g. 
        unshelve eapply exist. 
        1: eexists ?[st] ?[tm] ?[fm].
        5: { simpl. repeat split; reflexivity. }
        - auto. 
        - intros ρ'. apply mapped_roles_dom_fuels_gen.
          rewrite dom_insert_L. rewrite /mapped_roles.
          rewrite map_img_insert_L. rewrite flatten_gset_union. f_equal.
          { by rewrite flatten_gset_singleton. }
          etrans.
          { eapply mapped_roles_dom_fuels_gen. apply δ. }
          rewrite /mapped_roles.
          apply set_eq. clear -TM.  intros ρ'.
          rewrite !flatten_gset_spec. apply exist_proper. intros. 
          do 2 rewrite (and_comm _ (ρ' ∈ _)). apply iff_and_pre. intros.
          rewrite !elem_of_map_img. apply exist_proper. intros [ρ''].
          rewrite !lookup_delete_Some.
          symmetry. rewrite and_comm. apply iff_and_impl_helper.
          intros TM' [=]. subst.
          rewrite TM in TM'. inversion TM'. set_solver.
        - red. intros [ρ1] [ρ2] * NEQ. rewrite !lookup_insert_Some.
          intros [[[=] <-]| [? TM1]] [[[=] <-]| [? TM2]]; subst.
          + tauto.
          + apply (ls_inv δ) in TM2. set_solver.
          + apply (ls_inv δ) in TM1. set_solver.
          + eapply (ls_tmap_disj δ (asG ρ1) (asG ρ2)); eauto.
        - red. split; [| split]. 
          + rewrite map_Forall_lookup. intros [ρ'] Rρ' L.
            rewrite lookup_insert_Some in L. destruct L as [[[=] <-] | [? TM']].
            * set_solver. 
            * by apply (ls_inv δ) in TM'.
          + rewrite /is_unused.
            intros. rewrite -dec_dne.
            rewrite DOM_RM. 
            rewrite !dom_insert. rewrite !elem_of_union.
            apply Morphisms_Prop.or_iff_morphism.
            { set_solver. }
            etrans.
            2: { apply (ls_inv δ). }
            rewrite /is_unused. tauto. 
          + rewrite dom_insert_L dom_tmap_tl_fixed.
            apply mk_is_Some, elem_of_dom in TM.
            pose proof TM as TM'. rewrite dom_tmap_tl_fixed in TM'. 
            set_solver.
      Qed.

      End ExtTrans.

      Lemma tl_egs:
        (* role_enabled_model ((asG ρ'): fmrole (LM_Fair (LF := TlLF))) δ' <-> *)
        (* ρ' ∈ dom (ls_mapping δ'). *)
        forall (ρ': fmrole M) δ', enabled_group_singleton _ TlLF ρ' δ'. 
      Proof.
        eapply egs_helper.
        - apply tl_ls_map_restr.
        - intros. red. split; [| split]; try by apply δ1.
          intros. rewrite -ext_trans_same_unused.
          2: { left. eauto. }
          eapply (ls_inv δ1).
        - red. done.
        - apply tl_strong_FM. 
        - red. intros * L. split; [| split].
          + rewrite map_Forall_lookup. intros [ρ] S IN.
            apply lookup_fmap_Some in IN as (? & <- & IN).
            apply L in IN. set_solver.
          + intros. rewrite dom_fmap. apply L.
          + rewrite dom_fmap_L. apply L.
        - unshelve eapply step_no_en.
          4: exact TLFairLock. 
      Qed.

      Local Ltac simpl_prop P :=
          destruct P as [DOM [P | P]]; [| tauto]; destruct P as [P ?].

      Lemma allow_unlock_impl':
      {δ': lm_ls tl_model | @fair_lock.does_unlock _ FLP_Tl g δ /\
                            @fair_lock.disabled_st _ FLP_Tl g δ ->
                            let '(asG ρ) := g in
                            lm_ls_prop (allow_unlock_impl ρ (ls_under δ)) δ'}.
      Proof. 
        destruct (decide (@fair_lock.does_unlock _ FLP_Tl g δ /\
                            @fair_lock.disabled_st _ FLP_Tl g δ)) as [[LOCK DIS]|].
        2: { exists δ. tauto. }
        simpl in LOCK, DIS.
        destruct g as [ρ] eqn:GG.        
        destruct (ls_under δ) as [o t rm wf] eqn:ST.

        red in DIS. pose proof DIS as DIS'%disabled_group_disabled_role; [| apply tl_egs].
        apply disabled_equiv in DIS'.
        2: { apply has_lock_dom. by simpl_prop LOCK. }        

        edestruct (ext_trans_impl (allow_unlock_impl ρ (ls_under δ): fmstate M)) as [δ' PROP']. 
        { simpl_prop LOCK.
          apply disabled_group_singleton in DIS; [| apply tl_egs].
          apply unmapped_empty_dom in DIS; auto; [| apply tl_ls_map_restr].
          set_solver. }
        { rewrite ST. simpl.  
          simpl_prop LOCK. simpl_ρ ρ. subst.
          rewrite ST in LOCK. simpl in LOCK. 
          destruct decide; [| tauto]. 
          simpl. set_solver. }
        { rewrite /allow_unlock_impl. simpl.
          simpl_prop LOCK. simpl_ρ ρ. subst.
          rewrite ST in LOCK. simpl in LOCK. 
          rewrite ST. destruct decide; [| tauto].
          rewrite /tl_live_roles. simpl.
          rewrite map_filter_insert. simpl.
          rewrite !dom_insert.
          apply union_mono; [done| ].
          etrans; [| eapply (ls_fuel_dom δ)].
          rewrite ST. reflexivity. }
        eexists. by rewrite -ST.
      Qed. 

      Lemma allow_lock_impl':
      {δ': lm_ls tl_model | @fair_lock.does_lock _ FLP_Tl g δ /\
                            @fair_lock.disabled_st _ FLP_Tl g δ ->
                            let '(asG ρ) := g in
                            lm_ls_prop (allow_lock_impl ρ (ls_under δ)) δ'}.
      Proof. 
        destruct (decide (@fair_lock.does_lock _ FLP_Tl g δ /\
                            @fair_lock.disabled_st _ FLP_Tl g δ)) as [[LOCK DIS]|].
        2: { exists δ. tauto. }
        simpl in LOCK, DIS.
        destruct g as [ρ] eqn:GG.        
        destruct (ls_under δ) as [o t rm wf] eqn:ST.

        red in DIS. pose proof DIS as DIS'%disabled_group_disabled_role; [| apply tl_egs].
        apply disabled_equiv in DIS'.
        2: { apply does_lock_dom. by simpl_prop LOCK. }        

        edestruct (ext_trans_impl (allow_lock_impl ρ (ls_under δ): fmstate M)) as [δ' PROP']. 
        { simpl_prop LOCK.
          apply disabled_group_singleton in DIS; [| apply tl_egs].
          apply unmapped_empty_dom in DIS; auto; [| apply tl_ls_map_restr].
          set_solver. }
        { rewrite ST. simpl.  
          simpl_prop LOCK. simpl_ρ ρ. subst.
          destruct LOCK as [LOCK | LOCK].
          - simpl_ρ ρ; subst; rewrite ST in LOCK; simpl in LOCK;
            destruct decide; [| tauto];
            simpl; set_solver. 
          - simpl_ρ ρ; subst; rewrite ST in LOCK; simpl in LOCK. 
            destruct decide.
            { rewrite e in LOCK. congruence. }
            simpl. apply mk_is_Some, elem_of_dom in LOCK. set_solver. } 
        { rewrite /allow_lock_impl. simpl.
          simpl_prop LOCK. simpl_ρ ρ. subst.
          rewrite ST in LOCK, DIS'. simpl in LOCK. 
          rewrite ST.            
          destruct LOCK as [LOCK | LOCK]; simpl in LOCK. 
          - simpl_ρ ρ; subst; simpl in LOCK.  
            destruct decide; simpl in *.
            2: { tauto. } 
            rewrite /tl_live_roles. simpl.
            rewrite map_filter_insert. simpl.
            rewrite !dom_insert.
            apply union_mono; [done| ].
            etrans; [| eapply (ls_fuel_dom δ)].
            rewrite ST. reflexivity.
          - simpl_ρ ρ; subst; simpl in LOCK.  
            destruct decide; simpl in *.
            { rewrite e in LOCK. congruence. }
            rewrite /tl_live_roles. simpl.
            etrans; [| etrans]; [| eapply (ls_fuel_dom δ)| ].
            2: set_solver. 
            rewrite ST. reflexivity. }
        eexists. by rewrite -ST.
      Qed. 

    End ImplFunctions.
    
    Instance Tl_FLE_LM: @FairLockExt (LM_Fair (LF := TlLF)) 
                          (@FLP_LMF _ tl_FLP _ _ TlLF).
    eapply (FLE_LMF TLFairLock).
    - apply _.
    - intros. by apply tl_ls_map_restr.
    - intros. simpl.
      pose proof (proj1 (proj2 (ls_inv δ)) ρ). tauto.
    - apply tl_egs. 
    Defined.

    (* Set Printing Implicit. *)
    Definition Tl_LM_EM_EXT_KEEPS: ext_models.ext_keeps_asg (ELM := FL_EM Tl_FLE_LM).
      unshelve eapply LM_EM_EXT_KEEPS.
    Defined.

    (* TODO: move *)
    Lemma lm_ls_eq_PI `{LM: LiveModel G M LSI} (δ1 δ2: lm_ls LM):
      (ls_under δ1 = ls_under δ2 /\ ls_tmap δ1 = ls_tmap δ2 /\ ls_fuel δ1 = ls_fuel δ2) <->
      δ1 = δ2.
    Proof.
      split.
      2: { intros ->. tauto. }
      intros (?&?&?). destruct δ1, δ2. simpl in *. subst.
      f_equal; apply make_proof_irrel.
    Qed. 
    

    Instance Tl_FL_LM: FairLock
                         (LM_Fair (LF := TlLF))
                         FLP_Tl
                         Tl_FLE_LM
                         (fun tr => forall g, fair_by_group (ELM_ALM Tl_LM_EM_EXT_KEEPS) g tr).
    assert (forall ρ (δ: lm_ls tl_model), ls_tmap δ !! asG ρ = Some ∅ -> asG ρ ∈ dom (ls_tmap δ)) as IMPL. 
    { intros. rewrite elem_of_dom. eauto. }
    unshelve eapply FL_LM.
    2: exact (fun g δ => proj1_sig $ allow_lock_impl' g δ).
    1: exact (fun g δ => proj1_sig $ allow_unlock_impl' g δ).
    - intros [ρ] ??.
      destruct allow_unlock_impl' as [δ'' PROP]. simpl.       
      simpl. rewrite allows_unlock_impl_spec.
      
      etrans.
      2: { apply ZifyClasses.and_morph; [reflexivity| ].
           rewrite and_comm. eapply iff_and_pre. intros DIS.
           eapply iff_and_pre. intros DOM.
           apply ZifyClasses.or_morph.
           { apply ZifyClasses.and_morph; [reflexivity| ].
             rewrite disabled_group_singleton; [| apply tl_egs].
             rewrite unmapped_empty_dom; [| apply tl_ls_map_restr| auto].
             apply ZifyClasses.or_morph with (s1 := False); [| reflexivity].
             symmetry. apply iff_False_helper. eapply disabled_group_disabled_role; eauto.
             apply tl_egs. }             
           Unshelve. 2: exact False. red in DIS. tauto. }
      rewrite or_False False_or.
      etrans. 
      { rewrite !and_assoc. eapply iff_and_impl_helper. intros.
        eapply disabled_group_disabled_role.
        { apply tl_egs. }
        apply LM_map_empty_notlive. tauto. }
      etrans.
      2: { apply ZifyClasses.and_morph; [reflexivity| ].
           rewrite and_assoc and_comm. symmetry. apply iff_and_impl_helper.
           intros. split.
           2: { eapply elem_of_dom. set_solver. }
           apply LM_map_empty_notlive. tauto. }
      rewrite -!and_assoc. 

      enough (has_lock_st ρ (ls_under δ) ∧ ls_tmap δ !! asG ρ = Some ∅ ->
              ls_tmap δ' = <[asG ρ:={[ρ]}]> (ls_tmap δ) /\
              ls_fuel δ' = <[ρ:=tl_fl]> (ls_fuel δ) /\
              allow_unlock_impl ρ (ls_under δ) = ls_under δ'
              <-> δ'' = δ').
      { tauto. }

      intros (TM&LOCK).
      rewrite -lm_ls_eq_PI.
      specialize_full PROP.
      { simpl. repeat split; eauto.
        2: { apply LM_map_empty_notlive. tauto. }
        left. split; auto. right. apply LM_map_empty_notlive. tauto. }
      destruct PROP as (-> & -> & ->). set_solver.
    (* TODO: unify *)
    - intros [ρ] ??.
      destruct allow_lock_impl' as [δ'' PROP].        
      simpl. rewrite allows_lock_impl_spec.

      etrans.
      2: { apply ZifyClasses.and_morph; [reflexivity| ].
           rewrite and_comm. eapply iff_and_pre. intros DIS.
           eapply iff_and_pre. intros DOM.
           apply ZifyClasses.or_morph.
           { apply ZifyClasses.and_morph; [reflexivity| ].
             rewrite disabled_group_singleton; [| apply tl_egs].
             rewrite unmapped_empty_dom; [| apply tl_ls_map_restr| auto].
             apply ZifyClasses.or_morph with (s1 := False); [| reflexivity].
             symmetry. apply iff_False_helper. eapply disabled_group_disabled_role; eauto.
             apply tl_egs. }             
           Unshelve. 2: exact False. red in DIS. tauto. }
      rewrite or_False False_or.
      etrans. 
      { rewrite !and_assoc. eapply iff_and_impl_helper. intros.
        eapply disabled_group_disabled_role.
        { apply tl_egs. }
        apply LM_map_empty_notlive. tauto. }
      etrans.
      2: { apply ZifyClasses.and_morph; [reflexivity| ].
           rewrite and_assoc and_comm. symmetry. apply iff_and_impl_helper.
           intros. split.
           2: { eapply elem_of_dom. set_solver. }
           apply LM_map_empty_notlive. tauto. }
      rewrite -!and_assoc.


      enough (does_lock ρ (ls_under δ) ∧ ls_tmap δ !! asG ρ = Some ∅ ->
              ls_tmap δ' = <[asG ρ:={[ρ]}]> (ls_tmap δ) /\
              ls_fuel δ' = <[ρ:=tl_fl]> (ls_fuel δ) /\
              allow_lock_impl ρ (ls_under δ) = ls_under δ'
              <-> δ'' = δ').
      { tauto. }

      intros (TM&LOCK).
      rewrite -lm_ls_eq_PI.
      specialize_full PROP.
      { simpl. repeat split; eauto.
        2: { apply LM_map_empty_notlive. tauto. }
        left. split; auto. right. apply LM_map_empty_notlive. tauto. }
      destruct PROP as (-> & -> & ->). set_solver.

    Qed. 

  End TlFL. 

End TlLM. 

Opaque tl_gs.

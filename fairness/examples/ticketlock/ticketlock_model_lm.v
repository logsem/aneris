From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fuel lm_fair. 
From trillium.fairness.examples.ticketlock Require Import fair_lock ticketlock_model fair_lock_lm. 

Section TlLM.
  Let M := tl_fair_model.
  Let G := @FlG M.
  Let R := fmrole tl_fair_model.
  
  Context {n_roles: nat}.
  Let roles: gset R := dom $ snd $ tl_init_st' n_roles. 
  Let gs: gset G := set_map asG roles. 
  
  Definition LSI_Tl (st: fmstate M) (tm: groups_map) (fm: @fuel_map M) :=
    (* LSI_groups_fixed gs st tm fm /\ *) (* <- implied by last condition *)
    forall ρ, default ∅ (tm !! asG ρ) ⊆ {[ ρ ]} /\           
    (* ¬ is_unused ρ st <-> asG ρ ∈ dom tm.  *)
    dom tm = gs. 

  Definition tl_fl := 100. 
  
  Definition tl_model: LiveModel G M LSI_Tl :=
    {| lm_fl _ := tl_fl; |}.

  Instance tl_step_dec s1 ρ s2: Decision (fmtrans M s1 (Some ρ) s2).
  Proof.
    Local Ltac nostep := right; intros S; inversion S; subst; set_solver.
    destruct s1 as [o1 t1 rm1 wf1], s2 as [o2 t2 rm2 wf2].
    destruct (rm1 !! ρ) as [[s e]| ] eqn:RR.
    2: { nostep. }
    destruct e.
    2: { nostep. } 
    destruct s as [| k]. 
    { destruct (decide (
                      o2 = o1 /\ t2 = t1 + 1 /\ 
                      let next_en := if decide (o1 = t1) then false else true in
                      rm2 = <[ρ := (tl_U t1, next_en)]> rm1)) as [T| ?].
      - destruct T as (->&->&->).
        left. by constructor.
      - nostep. }
    destruct (decide (o1 ≠ k /\ o2 = o1 /\ t2 = t1 /\ rm2 = rm1)) as [T| ?].
    { inversion T as (?&->&->&->). left. by econstructor. }
    destruct (decide (k = o1 /\
                        let st' := (o1 + 1, t1, <[ρ := (tl_L, false)]> rm1) in
                        let st'' := advance_next st' in
                        (o2, t2, rm2) = st'')) as [T |]. 
    { destruct T as [-> ST2].
      left. simpl. red. simpl.
      rewrite ST2. by econstructor. }
    nostep.
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

  Instance tl_inh: Inhabited (lm_ls tl_model).
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
    - simpl. repeat split.
      + simpl. destruct lookup eqn:L; [| done].
        simpl. eapply @lookup_set_to_map in L.
        2, 3: apply _.
        2: set_solver.
        destruct L as (?&?&[=]). by subst.
      + rewrite dom_set_to_map_gset_gmap. set_solver.
  Qed.

  Let encode_rs := fun rs => match rs with | tl_U k => S k | _ => 0 end. 

  Instance tl_role_stage_Cnt: Countable tl_role_stage. 
  Proof using.
    eapply inj_countable' with
      (f := encode_rs)
      (g := fun i => match i with | 0 => tl_L | S i => tl_U i end).
    by intros [].
  Qed.

  (* Let foo (rm: gmap nat (tl_role_stage * bool)): gset (tl_role_stage * bool) := map_img rm.  *)

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
      destruct (rm !! ρ) as [[rs e] |] eqn:RR.
      2: { set_solver. }
      split.
      * intros O ? [=]; subst.
        specialize_full O; [reflexivity| ]. 
        simpl in O. lia.
      * intros O [??] [=] ->; subst.
        destruct t0; [done| ]. 
        specialize_full O; [reflexivity| ].
        done.
    - 
          
        

  Lemma tl_model_impl_step_fin (s1 : tl_st):
    {nexts: list tl_st | forall s2 oρ, tl_trans s1 oρ s2 -> s2 ∈ nexts}.
  Proof.
    destruct s1 as [o t rm wf] eqn:S.
    set nexts' :=
      o' ← [o; o + 1];
      t' ← [t; t + 1];
      ρ' ← elements (dom rm);
      s' ← [tl_U t; tl_L];
      e' ← [true; false];
      let rm' := <[ ρ' := (s', e') ]> rm in
      tl_state_wf
      mret (o', t', rm'). 
    set nexts := s :: 

  Instance tl_lm_dec_ex_step:
    ∀ τ δ1, Decision (∃ δ2, locale_trans δ1 τ δ2 (LM := tl_model)).
  Proof. 
    intros.
    pose proof (client_model_step_fin (ls_under δ1)) as [nexts NEXTS]. 
    apply locale_trans_ex_dec_fin with (steps := nexts).
    { intros. apply elem_of_list_In. eauto. }
    intros. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact client_model. 
    + red. intros ? [??].
      pose proof (mapped_roles_dom_fuels_gen (rearrange_roles_map (ls_tmap δ2) (dom (ls_tmap δ0)) τ0) ((ls_fuel δ2))) as R.             
      erewrite <- (proj1 R).
      2: { apply rrm_tmap_fuel_same_doms. }
      pose proof (ls_inv δ2) as LSI2. red in LSI2. 
      specialize (LSI2 _ ltac:(eauto)).
      by rewrite -mapped_roles_dom_fuels in LSI2. 
  Qed.
    

        
  Instance TlLF: lm_fair.LMFairPre tl_model.
  esplit; try by apply _.
  

End TlLM. 

Section TlFL.

  FL_LM

End TlFL. 

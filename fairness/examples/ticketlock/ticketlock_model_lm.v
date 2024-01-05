From trillium.fairness Require Import fuel. 
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
        
  Instance TlLF: lm_fair.LMFairPre tl_model.
  esplit; try by apply _.
  

End TlLM. 

Section TlFL.

  FL_LM

End TlFL. 

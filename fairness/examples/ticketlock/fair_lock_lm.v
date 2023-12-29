From trillium.fairness.examples.ticketlock Require Import fair_lock.
From trillium.fairness Require Import fuel lm_fair lm_fairness_preservation.
From trillium.fairness.ext_models Require Import ext_models.
From iris.proofmode Require Import tactics.
From stdpp Require Import base.


Section FairLockLM.
  
  Context `(FL: @FairLock M FLP FLE).

  Let R := fmrole M.
  (* For the lock model (and others that also don't fork),
     we suppose that every group contains up to one role, 
     and this role uniquely corresponds to that group.
     Therefore, LM here only provides stuttering steps. *)
  Inductive G := | asG (r: R).

  Instance G_eqdec: EqDecision G.
  solve_decision.
  Qed.

  Instance G_cnt: Countable G.
  eapply inj_countable' with (f := fun '(asG ρ) => ρ) (g := asG).
  by intros []. 
  Qed.  

  Context `(LM: LiveModel G M LSI). 
  Context (LF: LMFairPre LM).

  Let LMF := LM_Fair (LF := LF).

  Let lift_prop1 (P: R -> fmstate M -> Prop): 
    fmrole LMF -> lm_ls LM -> Prop := 
        fun g δ => let '(asG ρ) := g in
                 P ρ (ls_under δ). 
          (* exists ρ, *)
          (*   ls_tmap (δ: fmstate LMF) !! g = Some {[ ρ ]} /\ *)
          (*   P ρ (ls_under δ). *)

  (*TODO: move *)
  Lemma gset_singleton_dec `{Countable K}:
    forall (g: gset K), {k | g = {[ k ]}} + (forall k, g ≠ {[ k ]}).
  Proof.
    intros. 
    destruct (decide (g = ∅)) as [-> | NE].
    { right. set_solver. }
    apply finitary.set_choose_L' in NE as [k IN].
    erewrite union_difference_singleton_L with (x := k) (Y := g); auto.
    destruct (decide (g ∖ {[k]} = ∅)) as [-> | NE']. 
    2: { apply finitary.set_choose_L' in NE' as [k' IN'].
         right. intros k''.
         intros EQ. apply (@f_equal _ _ size) in EQ.
         rewrite size_union in EQ; [| set_solver].
         rewrite !size_singleton in EQ.
         assert (size (g ∖ {[k]}) = 0) as S0 by lia.
         apply size_empty_inv in S0. set_solver. }
    rewrite union_empty_r_L. left. eauto.
  Qed. 

  Instance lift_prop1_dec P
    (DECP: forall ρ st, Decision (P ρ st)):
    forall g δ, Decision (lift_prop1 P g δ).
  Proof. 
    intros [g] δ. rewrite /lift_prop1.
    solve_decision. 
  Qed.

  Let wf_placeholder: lm_ls LM -> Prop.
  Admitted.

  (* TODO: move, find existing? *)
  Instance gtb_dec: forall x y, Decision (x > y).
  Proof. 
    intros. 
    destruct (lt_eq_lt_dec x y) as [[? | ->] | ?].
    3: by left.
    all: right; lia.
  Qed. 

  Instance FLP_LMF: FairLockPredicates LMF.
  refine {| 
      can_lock_st := lift_prop1 can_lock_st;
      has_lock_st := lift_prop1 has_lock_st;
      active_st := fun '(asG ρ) δ => 
            ls_tmap (δ: fmstate LMF) !! (asG ρ) = Some {[ ρ ]} /\
            (active_st ρ (ls_under δ) \/ default 0 (ls_fuel δ !! ρ) > 0);
      is_unused := lift_prop1 is_unused;
      state_wf := wf_placeholder;
    |}.
  intros [?] ?. solve_decision. 
  Defined.

  Let lift_prop2 (P: fmrole M -> fmstate M -> fmstate M -> Prop):
    fmrole LMF -> lm_ls LM -> lm_ls LM -> Prop := 
        fun '(asG ρ) δ1 δ2 =>
            ls_tmap δ1 !! (asG ρ) = Some ∅ /\
            ls_tmap δ2 !! (asG ρ) = Some {[ ρ ]} /\              
            P ρ (ls_under δ1) (ls_under δ2).

  (* Let LM_active_exts (δ: fmstate LMF): gset (@fl_EI LMF) := *)
  (*       let active_under := fl_active_exts (ls_under δ) in *)
  (*       let g: G := @inhabitant G _ in *)
  (*       let lift := fun ι => match ι with *)
  (*                         | flU ρ => flU (default g (ls_mapping δ !! ρ)) (M := LMF) *)
  (*                         | flL ρ => flL (default g (ls_mapping δ !! ρ)) (M := LMF) *)
  (*                         end in *)
  (*       set_map lift active_under. *)

  Let allows_unlock := lift_prop2 allows_unlock. 
  Let allows_lock := lift_prop2 allows_lock.

  Instance lift_prop2_dec P
    (DECP: forall ρ st1 st2, Decision (P ρ st1 st2)):
    forall g δ1 δ2, Decision (lift_prop2 P g δ1 δ2).
  Proof.
    intros [g] δ1 δ2. rewrite /lift_prop2.
    solve_decision. 
  Qed.

  Instance allows_lock_ex_dec:
    forall δ g, Decision (∃ δ', allows_lock g δ δ'). 
  Proof using.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl. 
    { setoid_rewrite allows_lock_impl_spec.
      reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      can_lock_st ρ δ ∧ ¬ active_st ρ δ)). 
    2: { right. set_solver. }
    left. eexists {|        
        ls_under := allow_lock_impl ρ δ;
        ls_tmap := <[ asG ρ := {[ ρ ]} ]> (ls_tmap δ);
        ls_fuel := <[ ρ := 0 ]> (ls_fuel δ);
 |}.
    repeat split; eauto; try by apply a.
    simpl. by rewrite lookup_insert.
    Unshelve.
    1-4: admit. 
  Admitted. 


  Instance allows_unlock_ex_dec:
    forall δ g, Decision (∃ δ', allows_unlock g δ δ'). 
  Proof using.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl. 
    { setoid_rewrite allows_unlock_impl_spec.
      2: { admit. }
      reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      has_lock_st ρ δ ∧ ¬ active_st ρ δ)). 
    2: { right. set_solver. }
    left. eexists {|        
        ls_under := allow_unlock_impl ρ δ;
        ls_tmap := <[ asG ρ := {[ ρ ]} ]> (ls_tmap δ);
        ls_fuel := <[ ρ := 0 ]> (ls_fuel δ);
 |}.
    repeat split; eauto; try by apply a.
    simpl. by rewrite lookup_insert.
    Unshelve.
    1-4: admit. 
  Admitted. 

  Let tl_active_exts (δ: fmstate LMF): gset fl_EI := 
      set_map (flU (M := LMF)) 
          (filter (fun g => exists δ', allows_unlock g δ δ') (dom (ls_tmap δ)))
      ∪
      set_map (flL (M := LMF)) 
          (filter (fun g => exists δ', allows_lock g δ δ') (dom (ls_tmap δ))).
    

  Instance FLE_LMF: FairLockExt LMF.
  refine {|
      fair_lock.allows_unlock := allows_unlock;
      fair_lock.allows_lock := allows_lock;
      fair_lock.fl_active_exts := tl_active_exts;
    |}. 
  intros. simpl.
  unfold tl_active_exts.
  rewrite elem_of_union.
  rewrite !elem_of_map. repeat setoid_rewrite elem_of_filter.
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  rewrite or_comm. 
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  destruct ι; set_solver. 
  Defined.

  Lemma LM_EM_EXT_KEEPS: ext_keeps_asg
                              (ELM := (FL_EM FLE_LMF)).
  Proof.
    red.
  Admitted. 


  Lemma FL_LM_progress:
    @fair_lock_progress _ FLP_LMF (FL_EM FLE_LMF).
  Proof.
    red. intros.
    clear FAIR. 
    assert (∀ g: G,
               fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g tr) as FAIR. 
    { admit. (* parametrize FairLock with the desired notion of fairness *) }
    
    

  Instance FL_LM: FairLock LMF FLP_LMF FLE_LMF.
  esplit.
  12: { red. simpl. 
  

End FairLockLM.

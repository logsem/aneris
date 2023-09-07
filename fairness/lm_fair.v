From trillium.fairness Require Import fairness fuel fuel_ext.

Close Scope Z_scope.

Section LMFair.
  Context `{LM: LiveModel G M}.
  Context `{Countable G, Inhabited G}.
  Context `{EqDecision M, Inhabited (fmstate M)}.

  Global Instance FL_cnt: Countable (@FairLabel G (fmrole M)).
  Proof. 
    set (FL_alt := (G * (fmrole M) + G + unit)%type).
    set (to_alt := fun fl => match fl with
                          | Take_step ρ τ => inl $ inl (τ, ρ)
                          | Silent_step τ => inl $ inr τ
                          | Config_step => (inr tt): FL_alt
                          end).
    set (from_alt := fun (fl': FL_alt) => match fl' with
                             | inl (inl (τ, ρ)) => Take_step ρ τ
                             | inl (inr τ) => Silent_step τ
                             | inr _ => Config_step
                             end).
    eapply (inj_countable' to_alt from_alt).
    intros. by destruct x. 
  Qed. 
  
  Global Instance LS_eqdec: EqDecision (LiveState G M).
  Proof. Admitted. 

  (* Lemma ls_trans_lim δ1 l δ2 *)
  (*   (STEP: lm_ls_trans LM δ1 l δ2): *)
  (*   l ∈ potential_step_FLs δ1 l.  *)
  Instance lm_ls_trans_dec st1 l st2:
    Decision (lm_ls_trans LM st1 l st2).
  Proof.
    destruct l; simpl. 
    3: { right. intros []. tauto. }
    - repeat apply and_dec.
      + admit. 
      + solve_decision. 
      + rewrite /fuel_decr. admit. 
      + rewrite /fuel_must_not_incr.
        admit.
      + apply impl_dec; [solve_decision| ].
        admit.
      + admit.
      + solve_decision.
    - repeat apply and_dec.
      + admit.
      + admit. (* TODO: reuse *)
      + admit. (* TODO: reuse *)
      + solve_decision.
      + solve_decision.
  Admitted.


  Definition potential_step_FLs (st1: lm_ls LM) (τ: G): 
    gset (@FairLabel G (fmrole M)) :=
    {[ Silent_step τ ]} ∪ (set_map (fun ρ => Take_step ρ τ) (dom (ls_fuel st1))).

  Definition allowed_step_FLs δ1 τ δ2: gset (@FairLabel G (fmrole M)) :=
    filter (fun l => bool_decide (lm_ls_trans LM δ1 l δ2) = true)
      (potential_step_FLs δ1 τ).


  (* TODO: upstream *)
  (* Lemma not_elem_of_equiv_not_empty_L: *)
  (* ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} *)
  (*   {H2 : Union C}, *)
  (*   SemiSet A C → LeibnizEquiv C → *)
  (*   ∀ X : C, X ≠ ∅ ↔ (exists x : A, x ∈ X). *)
  Lemma gset_not_elem_of_equiv_not_empty_L:
  ∀ {A : Type} `{Countable A},
    ∀ (X : gset A), X ≠ ∅ ↔ (exists x : A, x ∈ X).
  Proof.
    intros. split.
    - by apply set_choose_L.
    - set_solver. 
  Qed. 

  Definition lm_lbl_matches_group (ℓ: lm_lbl LM) (τ: G) := 
    match ℓ with
    | Take_step _ τ' | Silent_step τ' => τ = τ'
    | Config_step => False
    end. 

  (* TODO: rename *)
  Definition locale_trans (st1: lm_ls LM) (τ: G) st2 :=
    exists ℓ, ls_trans (lm_fl LM) st1 ℓ st2 /\ lm_lbl_matches_group ℓ τ. 

  Lemma locale_trans_alt δ1 τ δ2:
    locale_trans δ1 τ δ2 <-> allowed_step_FLs δ1 τ δ2 ≠ ∅.
  Proof. 
    rewrite /allowed_step_FLs /locale_trans. 
    rewrite gset_not_elem_of_equiv_not_empty_L.
    setoid_rewrite elem_of_filter.
    rewrite /potential_step_FLs.
    setoid_rewrite elem_of_union. setoid_rewrite elem_of_singleton.
    setoid_rewrite elem_of_map. 
    rewrite -ls_same_doms. setoid_rewrite elem_of_dom.  
    setoid_rewrite bool_decide_eq_true. 
    split.
    - intros (ℓ & T & MATCH).
      eexists. split; eauto.
      destruct ℓ; simpl in MATCH; subst; try tauto.
      right. eexists. split; eauto. inversion T. set_solver. 
    - intros (?&STEP&POT).
      destruct POT as [-> | (?&->&MAP)].
      all: eexists; split; [eapply STEP| done]. 
  Qed.

  Instance locale_trans_ex_dec τ st1:
    Decision (exists st2, locale_trans st1 τ st2).
  Proof.
    (* intros.  *)
  Admitted.

  Global Definition LM_Fair: FairModel.
    refine {|
        fmstate := lm_ls LM;
        fmrole := G;
        fmtrans :=
          fun st1 oρ st2 => 
            match oρ with
            | Some τ => locale_trans st1 τ st2
            | _ => False
            end;
        live_roles δ := filter (fun τ => exists δ', locale_trans δ τ δ') (dom (ls_tmap δ));
      |}.
    (* - apply lm_ls_eqdec.  *)
    - apply @inhabitant in H0 as l. apply @inhabitant in H1 as st.  
      eapply populate. refine 
        {| ls_under := st; 
           ls_fuel := gset_to_gmap 0 (live_roles _ st);
           ls_mapping := gset_to_gmap l (live_roles _ st); |}.
      + by rewrite dom_gset_to_gmap.
      + set_solver.
    - intros ??? STEP.
      apply elem_of_filter. split; eauto.
      destruct STEP as (ℓ & STEP & MATCH). destruct ℓ; simpl in *; try done; subst.
      + destruct STEP as (_&MAP&_).
        eapply ls_mapping_tmap_corr in MAP as (?&?&?). eapply elem_of_dom; eauto.
      + destruct STEP as ([? MAP]&_). 
        eapply ls_mapping_tmap_corr in MAP as (?&?&?). eapply elem_of_dom; eauto.
  Defined.

  Lemma LM_live_roles_strong δ τ:
    τ ∈ live_roles LM_Fair δ <-> (exists δ', locale_trans δ τ δ').
  Proof.
    split.
    2: { intros [??]. eapply LM_Fair. simpl. eauto. }
    simpl. intros [??]%elem_of_filter. eauto.
  Qed.

  (* Useful in cases where the whole LM_Fair machinery cannot be used *)
  Definition group_enabled τ δ := exists δ', locale_trans δ τ δ'.

  Lemma LM_live_role_map_notempty δ τ
    (LIVE: τ ∈ live_roles LM_Fair δ):
    exists R, ls_tmap δ (LM := LM) !! τ = Some R /\ R ≠ ∅.
  Proof. 
    apply LM_live_roles_strong in LIVE as [? STEP].
    destruct STEP as (ℓ & T & MATCH).
    destruct ℓ; simpl in *; try done; subst. 
    - destruct T as (_&MAP&_).
      eapply ls_mapping_tmap_corr in MAP as (?&?&?).
      eexists. split; eauto. set_solver. 
    - destruct T as ([? MAP]&_). 
      eapply ls_mapping_tmap_corr in MAP as (?&?&?). 
      eexists. split; eauto. set_solver. 
  Qed. 

  Lemma LM_map_empty_notlive δ τ
    (MAP0: ls_tmap δ (LM := LM) !! τ = Some ∅ \/ ls_tmap δ (LM := LM) !! τ = None):
    τ ∉ live_roles LM_Fair δ. 
  Proof. 
    destruct (decide (τ ∈ live_roles LM_Fair δ)) as [LR| ]; [| done].
    apply LM_live_role_map_notempty in LR as (? & TMAP & NE).
    destruct MAP0; set_solver. 
  Qed. 
      
End LMFair.

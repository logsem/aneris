From trillium.fairness Require Import fairness fuel fuel_ext.


Close Scope Z_scope.

Section LMFair.
  Context `{LM: LiveModel G M}.
  Context `{Countable G, Inhabited G}.
  Context `{Inhabited (fmstate M)}.

  (* TODO: rename *)
  Definition locale_trans (st1: lm_ls LM) (τ: G) st2 :=
    ls_trans (lm_fl LM) st1 (Silent_step τ) st2 \/
    exists ρ, ls_trans (lm_fl LM) st1 (Take_step ρ τ) st2. 

  Instance locale_trans_ex_dec τ st1:
    Decision (exists st2, locale_trans st1 τ st2).
  Proof.
    (* intros.  *)
  Admitted.

  Global Instance lm_ls_eqdec: EqDecision (lm_ls LM).
  Proof. Admitted. 

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
      inversion STEP as [[STEP']|[? STEP']]. 
      + inversion STEP'. eapply ls_mapping_tmap_corr in H3 as (?&?&?).
        eapply elem_of_dom_2; eauto. 
      + inversion STEP' as (? & MAP & ?).
        eapply ls_mapping_tmap_corr in MAP as (?&?&?).
        eapply elem_of_dom_2; eauto. 
  Defined.

  Lemma LM_live_roles_strong δ τ:
    τ ∈ live_roles LM_Fair δ <-> (exists δ', locale_trans δ τ δ').
  Proof. 
    split.
    2: { intros [??]. eapply LM_Fair. simpl. eauto. }
    simpl. intros [??]%elem_of_filter. eauto.
  Qed. 

  Lemma LM_map_empty_notlive δ τ
    (MAP0: ls_tmap δ (LM := LM) !! τ = Some ∅ \/ ls_tmap δ (LM := LM) !! τ = None):
    τ ∉ live_roles LM_Fair δ. 
  Proof. 
    intros [? STEP]%LM_live_roles_strong. inversion STEP.
    - inversion H2. destruct H3 as [? MAP].
      eapply ls_mapping_tmap_corr in MAP as (?&?&?).
      destruct MAP0 as [? | ?]; [| congruence]. set_solver.
    - inversion H2. destruct H3 as [? [MAP _]].
      eapply ls_mapping_tmap_corr in MAP as (?&?&?).
      destruct MAP0 as [? | ?]; [| congruence]. set_solver.
  Qed. 

  Lemma LM_live_role_map_notempty δ τ
    (LIVE: τ ∈ live_roles LM_Fair δ):
    exists R, ls_tmap δ (LM := LM) !! τ = Some R /\ R ≠ ∅.
  Proof. 
    apply LM_live_roles_strong in LIVE as [? STEP]. inversion STEP.
    - inversion H2. destruct H3 as [? MAP].
      eapply ls_mapping_tmap_corr in MAP as (?&?&?). eexists. split; eauto.
      set_solver.
    - inversion H2. destruct H3 as [? [MAP _]].
      eapply ls_mapping_tmap_corr in MAP as (?&?&?). eexists. split; eauto.
      set_solver.
  Qed. 
      
End LMFair.

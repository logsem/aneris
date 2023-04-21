From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness.examples.ticketlock Require Import set_map_properties.

(* TODO: can it be generalized to Model? *)
Section ExtModels.
  Context (M: FairModel).
  
  Context {EI: Type}. (* indexes over external transitions *)
  Context {DecEI: EqDecision EI} {CntEI: Countable EI}.
  Context (ETs: EI -> relation (fmstate M)). 

  (* Ensures that in any state there is only a finite amount 
     of possible external transitions, even if EI is infinite *)
  Context (active_exts: fmstate M -> gset EI). 
  Hypothesis (active_exts_spec: forall st ι, ι ∈ active_exts st <-> ∃ st', ETs ι st st').


  Inductive env_role := env (i: EI).
  Definition ext_role: Type := (fmrole M + env_role). 

  Global Instance env_role_EqDec: EqDecision env_role. 
  Proof using -DecEI. clear -DecEI. solve_decision. Qed. 

  Global Instance env_role_cnt: Countable env_role. 
  Proof.
    refine {| 
        encode r := match r with | env i => encode i end;
        decode i := match (decode i) with | Some r => Some (env r) | None => None end
      |}.
    intros. destruct x.
    by rewrite decode_encode.
  Qed.

  Inductive ext_trans: fmstate M -> option ext_role -> fmstate M -> Prop :=
  | ext_model_step s1 ρ s2 (STEP: fmtrans M s1 (Some ρ) s2):
    ext_trans s1 (Some (inl ρ)) s2
  | ext_ext_step s1 s2 ι (REL: ETs ι s1 s2):
    ext_trans s1 (Some (inr (env ι))) s2. 

  Definition ext_live_roles (st: fmstate M): gset ext_role :=
    set_map inl (live_roles M st) ∪
    set_map (inr ∘ env) (active_exts st). 

  Lemma ext_live_spec:
    ∀ s ρ s', ext_trans s (Some ρ) s' → ρ ∈ ext_live_roles s.
  Proof using.
    intros s ρ s' TRANS. unfold ext_live_roles.
    inversion TRANS; subst; simpl in *.
    - apply elem_of_union_l. apply elem_of_map_2. 
      eapply fm_live_spec; eauto. 
    - apply elem_of_union_r.
      rewrite set_map_compose_gset. 
      do 2 apply elem_of_map_2.
      apply active_exts_spec. eauto.
  Qed.
  
  Definition ext_model: FairModel.
  Proof using All. 
    refine({|
              fmstate := fmstate M;
              fmrole := ext_role;
              fmtrans := ext_trans;
              live_roles := ext_live_roles;
              fm_live_spec := ext_live_spec
            |}).
    apply M. 
  Defined.

End ExtModels. 

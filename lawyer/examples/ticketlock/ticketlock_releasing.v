From iris.proofmode Require Import tactics.
From lawyer.obligations Require Import obligations_logic obligations_model env_helpers.
From lawyer.examples.ticketlock Require Import fair_lock ticketlock releasing_lock.


Section TicketlockReleasing.
  Context `{OP: OP_HL DegO LvlO LIM_STEPS} `{EM: ExecutionModel heap_lang M}.

  Context (L__tl: gset om_hl_Level) (l__o : om_hl_Level)  
    (BOUND__o: ∀ l, l ∈ L__tl → lvl_lt l__o l)
    (l__acq : om_hl_Level)
    (IN_ACQ: l__acq ∈ L__tl).   

  Context (d0 d1 d2 d3 d4 d5: om_hl_Degree)
    (DEG01: deg_lt d0 d1) (DEG12: deg_lt d1 d2) (DEG23: deg_lt d2 d3)
    (DEG34: deg_lt d3 d4) (DEG45: deg_lt d4 d5).

  Context (LB_SB: S tl_exc ≤ LIM_STEPS).

  Program Definition TLPreInstance :=
    TLPre d1 d2 d3 d4  _ _ _ l__acq (OP := OP) (EM := EM).
  Solve All Obligations with eauto. 
  Fail Next Obligation.

  Program Definition TLInstance :=
    TL_FL d0 d1 d2 d3 d4  _ _ _ _ _ l__acq (OP := OP) (EM := EM).
  Solve Obligations with eauto. 
  Fail Next Obligation.  

  Program Definition RFL_FL_TL := @RFL_FL _ _ _ OP _ EM _ TLInstance l__o _ l__acq _ d5 _.
  Next Obligation.
    simpl. intros ?. rewrite /lvls_acq elem_of_singleton. intros ->.
    by apply BOUND__o. 
  Qed.
  Next Obligation.
    simpl. by rewrite /lvls_acq elem_of_singleton.
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed. 
  Fail Next Obligation.

  (** here we state that (wrappers over) ticketlock methods 
      satisfy the sequential lock specification,
      if the spec's parameters (rfl_d, rfl_lvls and rfl_sb_fun) are chosen 
      according to the OM parameters which in turn satisfy conditions in Context *)
  Definition RFL_FL_TL': ReleasingFairLock := {|
    rfl_newlock := method_aux tl_newlock;
    rfl_acquire := method_aux' tl_acquire;
    rfl_release := method_aux tl_release;
    rfl_d := d5;
    rfl_lvls := {[ l__acq; l__o ]};
    rfl_sb_fun := rfl_fl_sb_fun_impl tl_c__cr tl_fl_B;

    (*******)
    rfl_newlock_spec := @rfl_newlock_spec _ _ _ _ _ _ RFL_FL_TL;
    rfl_acquire_spec := @rfl_acquire_spec _ _ _ _ _ _ RFL_FL_TL;
    rfl_release_spec := @rfl_release_spec _ _ _ _ _ _ RFL_FL_TL;
    rfl_locked_excl := @rfl_locked_excl _ _ _ _ _ _ RFL_FL_TL;
    rfl_locked_sgn := @rfl_locked_sgn _ _ _ _ _ _ RFL_FL_TL;
  |}.

End TicketlockReleasing.

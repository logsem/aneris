From trillium.fairness.examples.spinlock Require Import spinlock_sc.


Close Scope Z_scope.

Opaque spinlock_model_impl.
Opaque spinlock_model.
Opaque program. 
Opaque program_init_fuels.
Opaque spinlock_model_impl. 
Opaque sm_fuel. 

Section LocksCompositionModel.


  Let sl_st := fmstate spinlock_model_impl.
  Let sl_role := fmrole spinlock_model_impl.

  (* TODO: how many 'option's should be there? *)
  Definition comp_state: Type := option sl_st * option sl_st * option nat.

  Inductive c_role := ρc. 
  Definition comp_role: Type := (sl_role + sl_role) + c_role.

  Inductive comp_trans: comp_state -> option comp_role -> comp_state -> Prop :=
  | ct_sl_step_1 s s' ρ os2 oc
      (STEP1: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (Some s, os2, oc) (Some $ inl $ inl ρ) (Some s', os2, oc)
  | ct_sl_step_2 s s' ρ os1 oc
      (STEP2: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (os1, Some s, oc) (Some $ inl $ inr ρ) (os1, Some s', oc)
  | cl_c_step os1 os2 c:
    comp_trans (os1, os2, Some (S c)) (Some $ inr ρc) (os1, os2, Some c)
  | cl_sl_init oc s1 s2:
    comp_trans (None, None, oc) (Some $ inr ρc) (Some s1, Some s2, oc)
  .

  Global Instance c_role_EqDec: EqDecision c_role.
  Proof. solve_decision. Defined.

  (* Global Instance comp_role_EqDec: EqDecision comp_role. *)
  (* Proof. solve_decision. Qed. *)

  Global Instance c_role_Cnt: Countable c_role.
  Proof.
    eapply @inj_countable' with (f := fun _ => ()) (g := fun _ => ρc).
    { apply unit_countable. }
    by intros [].
  Defined. 
    
  Global Instance comp_role_Cnt: Countable comp_role.
  Proof using. 
    (* Set Printing All. *)
    rewrite /comp_role.
    apply sum_countable. 
  Defined. 

  
  (* Compute (from_option S 55 None).  *)

  Definition comp_lr (st: comp_state): gset (comp_role) :=
    let get_lr (s: option sl_st) := from_option (live_roles _) ∅ s in 
    match st with 
    | (os1, os2, oc) => set_map (inl ∘ inl) (get_lr os1) ∪
                       set_map (inl ∘ inr) (get_lr os2) ∪
                       if (bool_decide ((os1, os2) = (None, None)) || (0 <? (from_option id 0 oc)))
                       then {[ inr ρc ]} else ∅ 
    end.
                                  

  (* TODO: proven in ticketlock dir *)
  Lemma set_map_compose_gset {A1 A2 A3: Type}
    `{EqDecision A1} `{EqDecision A2} `{EqDecision A3}
    `{Countable A1} `{Countable A2} `{Countable A3}
    (f: A2 -> A3) (g: A1 -> A2) (m: gset A1):
    set_map (f ∘ g) m (D:=gset _) = set_map f (set_map g m (D:= gset _)).
  Proof using. Admitted. 

  Definition comp_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := comp_state; 
        fmrole := comp_role;
        fmtrans := comp_trans;
        live_roles := comp_lr;
    |}).
    intros ??? TRANS. rewrite /comp_lr. inversion TRANS; subst.
    1: do 2 apply elem_of_union_l. 2: apply elem_of_union_l, elem_of_union_r. 
    1, 2: rewrite set_map_compose_gset; do 2 apply elem_of_map_2;
          eapply fm_live_spec; done. 
    all: apply elem_of_union_r; rewrite orb_true_intro; set_solver. 
  Defined.

  Definition add_fuel_1 := 3. 
  Definition add_fuel_2 := 3. 
  Definition add_fuel_3 := 1. 
  (* TODO: generalize? *)
  Definition comp_model: LiveModel heap_lang comp_model_impl :=
    {| lm_fl _ := sm_fuel + add_fuel_1 + add_fuel_2 + add_fuel_3; |}.  

  (* Definition comp_st_init (n: nat): fmstate comp_model_impl :=  *)
  (*   (None: option sl_st, None: option sl_st, n).  *)

End LocksCompositionModel.

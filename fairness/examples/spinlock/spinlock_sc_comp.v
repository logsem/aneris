From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From trillium.fairness.examples.spinlock Require Import spinlock_sc.


Close Scope Z_scope.
 
Opaque spinlock_model_impl.
Opaque spinlock_model.
Opaque program. 

Section LocksCompositionModel.


  Let sl_st := fmstate spinlock_model_impl.
  Let sl_role := fmrole spinlock_model_impl.

  Definition comp_state: Type := option sl_st * option sl_st * nat.

  Inductive c_role := ρc. 
  Definition comp_role: Type := (sl_role + sl_role) + c_role.

  Inductive comp_trans: comp_state -> option comp_role -> comp_state -> Prop :=
  | ct_sl_step_1 s s' ρ os2 c
      (STEP1: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (Some s, os2, c) (Some $ inl $ inl ρ) (Some s', os2, c)
  | ct_sl_step_2 s s' ρ os1 c
      (STEP2: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (os1, Some s, c) (Some $ inl $ inr ρ) (os1, Some s', c)
  | cl_c_step os1 os2 c:
    comp_trans (os1, os2, S c) (Some $ inr ρc) (os1, os2, c)
  | cl_sl_init c s1 s2:
    comp_trans (None, None, c) (Some $ inr ρc) (Some s1, Some s2, c)
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
    | (os1, os2, c) => set_map (inl ∘ inl) (get_lr os1) ∪
                       set_map (inl ∘ inr) (get_lr os2) ∪
                       if (bool_decide ((os1, os2) = (None, None)) || (0 <? c))
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

  Definition comp_model: LiveModel heap_lang comp_model_impl :=
    {| lm_fl _ := 2%nat; |}.  

  (* Definition comp_st_init (n: nat): fmstate comp_model_impl :=  *)
  (*   (None: option sl_st, None: option sl_st, n).  *)

End LocksCompositionModel.


Section LocksCompositionCode.

  (* Definition comp: expr := *)
  (*   let: "l" := newlock #() in *)
  (*   ((Fork (client "l") ) ;; (Fork (client "l") )). *)

  Definition comp: val :=
  λ: <>,
    let: "x" := ref #1 in
    (Fork (program #()) ;;
     Fork (program #())) ;;
    "x" <- #2.

  Class compPreG Σ := {
     sl1PreG :> spinlockPreG Σ;
     sl2PreG :> spinlockPreG Σ;
  }.
  

End LocksCompositionCode. 


Section Utils.

  (* TODO: make it the main definition *)
  Definition fuels_ge_alt_impl {A: Type} `{Countable A} (fs: gmap A nat) (b: nat) :=
    map_Forall (fun _ n =>  b <= n) fs. 

  (* TODO: make it the main definition *)
  Definition fuels_ge_alt {M} (fs: gmap (fmrole M) nat) (b: nat) :=
    map_Forall (fun _ n =>  b <= n) fs.  

  Lemma fuels_ge_equiv_defs {M} (fs: gmap (fmrole M) nat) (b: nat):
    fuels_ge fs b <-> fuels_ge_alt fs b. 
  Proof. done. Defined. 

  Global Instance fuels_ge_alt_impl_dec {A: Type} `{Countable A} 
    (fs: gmap A nat) (b: nat): 
    Decision (fuels_ge_alt_impl fs b).
  Proof.
    apply map_Forall_dec. solve_decision. 
  Defined.

  Lemma fge_impl {M: FairModel} (fs: gmap (fmrole M) nat) b:
    fuels_ge_alt_impl fs b -> fuels_ge fs b.
  Proof using. done. Qed. 

  Global Instance fuels_ge_alt_dec {M} fs b: Decision (@fuels_ge_alt M fs b).
  Proof.
    apply map_Forall_dec. solve_decision. 
  Defined. 

  (* TODO: instance of Proper for 'iff' and Decision  *)
  Global Instance fuels_ge_dec {M} fs b: Decision (@fuels_ge M fs b).
  Proof. 
    destruct (fuels_ge_alt_dec fs b) as [F | F].
    - left. by apply fuels_ge_equiv_defs. 
    - right. intros ?. destruct F. by apply fuels_ge_equiv_defs.
  Defined. 

End Utils.

Section LocksCompositionProofs.
  Context `{LM: LiveModel heap_lang Mdl} `{!heapGS Σ LM} {COMP_PRE: compPreG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ Mdl _ _ Σ comp_model_impl}.
  Context `{PMP: @PartialModelPredicates _ _ LM _ _ _ _ _ comp_model PMPP}.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Lemma comp_spec tid (P: iProp Σ):
    {{{ partial_model_is (None, None, 2)  ∗ 
        partial_free_roles_are ∅ ∗ 
        has_fuels tid {[ inr ρc:=2 ]} (PMPP := PMPP) }}}
      comp #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using. 
    iIntros (Φ) "(ST & NOFREE & FUELS) POST". rewrite /comp.

    (* iDestruct ((has_fuels_ge_S_exact 1) with "FUELS") as "FUELS".  *)
    iDestruct (has_fuels_ge_S_exact 1 with "FUELS") as "FUELS".
    { compute_done. }
    foobar. 
    iApply wp_lift_pure_step_no_fork; auto.
    2: do 3 iModIntro; iFrame. 
    1: set_solver. 
    iIntros "FUELS"; simpl.
    repeat rewrite fmap_insert. simpl. rewrite fmap_empty. simpl.
    
    


End LocksCompositionProofs.

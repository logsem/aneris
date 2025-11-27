From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_model.
From heap_lang Require Import lang notation. 


(* Local Definition hl_nil: val := NONEV.  *)
(* Local Definition hl_cons (v l: val): val := SOMEV (v, l). *)

Close Scope Z. 

Inductive is_hl_list (P: val -> Prop) : val -> Prop :=
  | hl_list_nil : is_hl_list P NONEV
  | hl_list_cons v l (LIST: is_hl_list P l) (Pv: P v):
    is_hl_list P (SOMEV (v, l))
.


Definition hl_list_map: val :=
  rec: "lm" "f" "l" :=
    Case "l"
      (λ: <>, NONE)
      (λ: "vl",
         let: "v'" := "f" (Fst "vl") in
         let: "l'" := "lm" "f" (Snd "vl") in
         SOME (Pair "v'" "l'") )
  .


Fixpoint hl_list_size (l: val): nat :=
  match l with
  | NONEV => 0
  | SOMEV (_, l') => S $ hl_list_size l'
  | _ => 0 (** we only use this function on lists *)
  end. 


Section ListMapSpec.
  Context {Σ: gFunctors}. 
  
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.

  Context {OHE: OM_HL_Env OP EM Σ}.

  Notation "'Degree'" := (om_hl_Degree).
  Context (d: Degree).

  Existing Instance OHE.

  Context (f: val) (n: nat) (P Q: val -> Prop) (f_inv: iProp Σ).
  Context (F_INV_PERS: Persistent f_inv). 
  Context (F_SPEC: forall τ π a, ⊢ 
            {{{ cp_mul π d n ∗ th_phase_eq τ π ∗ ⌜ P a ⌝ ∗ f_inv }}}
              f a @ τ
            {{{ v, RET v; th_phase_eq τ π ∗ ⌜ Q v ⌝ }}}).

  Let K := 20.

  Definition hl_map_fuel (l: val) := (S $ hl_list_size l) * (K + n). 

  Lemma list_map_spec' τ π (l: val)
    (LIST: is_hl_list P l):
    cp_mul π d (hl_map_fuel l) -∗ 
    th_phase_eq τ π -∗
    f_inv -∗
    WP hl_list_map f l @τ {{ l', th_phase_eq τ π ∗ ⌜is_hl_list Q l'⌝ }}.
  Proof using F_SPEC F_INV_PERS. 
    iIntros "CPS PH #F_INV".
    iInduction LIST as [| ] "IH"; rewrite /hl_list_map. 
    { pure_steps. 
      wp_bind (Rec _ _ _)%E.
      pure_steps.
      iFrame. iPureIntro.
      by constructor. }
    rewrite /hl_map_fuel. 
    rewrite (Nat.mul_succ_l (hl_list_size $ InjRV _)).
    iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]".
    iSpecialize ("IH" with "CPS'"). 
    iDestruct (cp_mul_split with "CPS") as "[CPS CPSf]".
    simpl. 
    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fst _)%E. pure_steps.
    wp_bind (f _)%E. 
    iApply (F_SPEC with "[$CPSf $PH $F_INV]").
    { done. }
    iIntros "!>" (v') "[PH %Qv']".
    
    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    wp_bind (Snd _)%E. do 2 pure_step_cases. 
    wp_bind (App _ _ _)%E.
    iApply (wp_wand with "[IH PH]").
    { iApply ("IH" with "[$]"). } 

    simpl. iIntros (h) "(PH & %LIST')".
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (Pair _ _)%E. pure_steps.
    iFrame. iPureIntro. by constructor.
  Qed.

  Lemma list_map_spec τ π (l: val):
    {{{ cp_mul π d (hl_map_fuel l) ∗ th_phase_eq τ π ∗ 
        ⌜ is_hl_list P l ⌝ ∗ f_inv }}}
      hl_list_map f l @ τ
    {{{ l', RET l'; th_phase_eq τ π ∗ ⌜ is_hl_list Q l' ⌝ }}}.
  Proof using F_SPEC F_INV_PERS.
    iIntros (Φ) "(CPS & PH & %LIST & #F_INV) POST".
    iApply (wp_wand with "[-]"). 
    { iApply wp_frame_step_r'. iSplitR "POST"; [| iAccu]. 
      by iApply (list_map_spec' with "[$] [$]"). }
    simpl.
    iIntros "% ([??] & POST)". iApply "POST". iFrame.
  Qed.

End ListMapSpec. 


From lawyer.nonblocking Require Import om_wfree_inst.

Section ListMapWFree.

  Context `(F_WFREE: WaitFreeSpec f).

  Definition hlm_is_init_st (c: cfg heap_lang) :=
    wfs_is_init_st _ F_WFREE c.

  Definition hlm_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ} :=
    wfs_mod_inv _ F_WFREE. 

  (* wfs_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} :: *)
  (*   Persistent wfs_mod_inv; *)

  Lemma hlm_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}:
    forall c (INIT: hlm_is_init_st c), ⊢ hl_phys_init_resource c ={⊤}=∗ hlm_mod_inv.
  Proof using. apply wfs_init_mod. Qed.

  Let map_f: val := λ: "v", hl_list_map f "v".

  Lemma hlm_spec:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    τ π (l: val),
    {{{ cp_mul π d_wfr0 (S $ hl_map_fuel (wfs_F _ F_WFREE) l) ∗ th_phase_eq τ π ∗
        (let _: heap1GS Σ := iem_phys HeapLangEM EM in hlm_mod_inv ) ∗
        ⌜ is_hl_list (fun _ => True) l ⌝
    }}}
      App map_f l @ τ
    {{{ v, RET v; th_phase_eq τ π }}}.
  Proof using.
    simpl. intros.
    iIntros "(CPS & PH & #INV & %LIST) POST". rewrite /map_f.
    pure_step. 

    iApply (list_map_spec with "[-POST]").
    3: { iFrame. iSplit; [| iApply "INV"]. done. }
    { apply _. }
    { Unshelve. 2: exact (fun _ => True).
      iIntros "**" (?). iIntros "!> (?&?&?&?) POST".
      iApply (wfs_spec _ F_WFREE with "[-POST]").
      2: { iIntros "!> **". iApply "POST". iSplit; done. }
      iFrame. }
    iIntros "!> % (?&?)". by iApply "POST".
  Qed.
      
End ListMapWFree. 

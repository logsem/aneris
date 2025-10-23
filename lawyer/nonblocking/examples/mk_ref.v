From iris.proofmode Require Import tactics.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_model.
From lawyer.nonblocking Require Import pwp.
From lawyer.nonblocking.logrel Require Import logrel.
From heap_lang Require Import lang sswp_logic heap_lang_defs tactics.


Section SimpleExample.

  Definition mk_ref: val  :=
    λ: "v",
      let: "l" := ref "v" in
      "l"
  .

  Definition mk_ref_inv {Σ}: iProp Σ := ⌜ True ⌝.

  Lemma mk_ref_init_inv {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ}
    (c: cfg heap_lang):
     hl_phys_init_resource c ={⊤}=∗ mk_ref_inv.
  Proof using. set_solver. Qed.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.

  Notation "'Degree'" := (om_hl_Degree).
  Context (d: Degree).

  Existing Instance OHE. 

  Lemma mk_ref_spec τ π q (a: val):
    {{{ cp_mul π d 5 ∗ th_phase_frag τ π q }}}
        mk_ref a @ τ
    {{{ (l: loc), RET #l; l ↦ a ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH) POST". rewrite /mk_ref.
    pure_steps.
    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iModIntro. iIntros (l) "L _".
    MU_by_burn_cp.
    pure_steps.
    wp_bind (Rec _ _ _)%E. pure_steps.
    iApply "POST". by iFrame.
  Qed.


End SimpleExample.


From lawyer.nonblocking Require Import om_wfree_inst. 

Lemma mk_ref_wfree_init_inv:
  ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ} (c : cfg heap_lang),
    (fun _ => True) c ->
    hl_phys_init_resource c ={⊤}=∗ mk_ref_inv.
Proof using.
  iIntros "**". iApply (mk_ref_init_inv with "[$]").
Qed. 

Lemma mk_ref_wfree_spec:
  ∀ (M : Model) (EM : ExecutionModel heap_lang M) (Σ : gFunctors) 
    (OHE : OM_HL_Env OP_HL_WF EM Σ) (τ : locale heap_lang) 
    (π : Phase) (q : Qp) (a : val) (Φ : val → iPropI Σ),
    cp_mul π d_wfr0 5 ∗ th_phase_frag τ π q ∗
    (λ (M0 : Model) (EM0 : ExecutionModel heap_lang M0) 
       (Σ0 : gFunctors) (_ : OM_HL_Env OP_HL_WF EM0 Σ0), mk_ref_inv)
      M EM Σ OHE -∗
    ▷ (∀ v : val, th_phase_frag τ π q -∗ Φ v) -∗
    WP mk_ref a @τ {{ v, Φ v }}.
Proof using.
  intros. simpl. 
  iIntros "(CPS & PH & #INV) POST".
  iApply (mk_ref_spec with "[-POST]").
  { iFrame. }
  iIntros "!> % (?&?)". iApply "POST". iFrame.
Qed.

From iris.base_logic Require Import invariants.

Lemma mk_ref_safety_spec
  {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}
  :
  (* ∀ (Σ : gFunctors) (H : irisG heap_lang LoopingModel Σ)  *)
  (*                       (H0 : heap1GS Σ), *)    
    (* let _ := irisG_looping HeapLangEM (lG := hG) in  *)
    ⊢ persistent_pred.pers_pred_car interp mk_ref.
Proof using.
  iIntros "**". rewrite interp_unfold /mk_ref /=.
  iModIntro. iIntros (τ v) "IIv".

  iApply sswp_pwp; [done| ].
  iModIntro.
  iApply sswp_pure_step; [done| ].
  do 3 iModIntro.
  simpl. 

  (* Set Printing Coercions. *)
  (* Unset Printing Notations. *)
  iApply (wp_bind [AppRCtx _]). 
  iApply sswp_pwp; [done| ].
  iModIntro.
  iApply wp_alloc. iIntros "!>" (l) "L _".
  do 2 iModIntro. simpl.

  iApply wp_value.

  iApply (wp_bind [AppLCtx _]). 
  iApply sswp_pwp; [done| ].
  iApply sswp_pure_step; [done| ].
  do 3 iModIntro. simpl.

  iApply wp_value.
  
  iApply sswp_pwp; [done| ].
  iApply sswp_pure_step; [done| ].
  do 4 iModIntro. simpl.

  iApply wp_value.

  rewrite {2}interp_unfold. simpl.
  iExists _. iSplitR; [done| ].  
  iApply inv_alloc. iExists _. iFrame.
Qed.
  

Definition mk_ref_WF_spec: WaitFreeSpec mk_ref := {|
  wfs_init_mod Σ _ _ := mk_ref_wfree_init_inv;
  wfs_spec := mk_ref_wfree_spec;
  wfs_safety_spec := @mk_ref_safety_spec;
|}.

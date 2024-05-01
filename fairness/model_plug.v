From trillium.fairness Require Import resources execution_model fairness. 
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.

Section ModelPlug.
  Context `{EM: ExecutionModel Λ M__glob}.
  Context `{eGS: em_GS Σ}. 

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}.
  Context {lifted_roles: fmstate M -> gset (fmrole M)}.

  Definition local_rule (P Q: iProp Σ) (ρ: fmrole M): iProp Σ :=
    □ (∀ (δ: fmstate M), P ∗ msi δ ==∗ 
        ∃ δ', Q ∗ msi δ' ∗ ⌜ fmtrans M δ (Some ρ) δ' ⌝ ∗ ⌜ lifted_roles δ' ⊆ lifted_roles δ ⌝). 

  Section MP.
    Context `{invGS_gen HasNoLc Σ}.
    (* Context (lift_ctx: iProp Σ). *)
    Context (ε: coPset).

    Definition role_lift (τ: locale Λ) (gl: fmrole M) (lift_ctx: iProp Σ): iProp Σ :=
      ∀ P Q, 
        □ (local_rule P Q gl -∗
           ∀ (extr: execution_trace Λ) (auxtr: auxiliary_trace M__glob) c2,
             lift_ctx ∗
             P ∗ 
             em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ∗
             ⌜ locale_step (trace_last extr) (Some τ) c2 ⌝ 
             ={ ε }=∗
             ∃ (δ2 : M__glob) (ℓ : mlabel M__glob),
             lift_ctx ∗
             Q ∗
             em_msi c2 δ2 (em_GS0 := eGS) ∗
             ⌜em_valid_state_evolution_fairness (extr :tr[ Some τ ]: c2) (auxtr :tr[ ℓ ]: δ2)⌝).

    Global Instance RL_pers: forall τ ρ lc, Persistent (role_lift τ ρ lc).
    Proof. apply _. Qed.    

  End MP.

  Section CWP.
    Context `{!irisG Λ M__glob Σ}.
        
    Let RL := @role_lift iris_invGS. 
                
    Definition cwp (e: expr Λ) (Φ: val Λ -> iProp Σ) (s: stuckness) (ε__wp ε__lift: coPset) (τ: locale Λ) (ρ: fmrole M): iProp Σ :=
      ∀ (lift_ctx: iProp Σ), lift_ctx -∗ RL ε__lift τ ρ lift_ctx  -∗ 
                              WP e @ s ; τ ; ε__wp {{ v, Φ v ∗ lift_ctx }}. 

    Lemma cwp_bind K (e: expr Λ) (Φ: val Λ -> iProp Σ) (s: stuckness) (ε__wp ε__lift: coPset) (τ: locale Λ) (ρ: fmrole M):
      cwp e (fun v => cwp (ectx_fill K (of_val v)) Φ s ε__wp ε__lift τ ρ) s ε__wp ε__lift τ ρ ⊢
      cwp (ectx_fill K e) Φ s ε__wp ε__lift τ ρ. 
    Proof.
      iIntros "STEP".
      rewrite /cwp. iIntros (LC) "LC #RL".
      iApply wp_bind.
      iSpecialize ("STEP" $! LC with "LC RL").
      iApply (wp_strong_mono with "STEP").
      1, 2: reflexivity.
      iIntros "* [WP LC]".
      iModIntro. iApply ("WP" with "[LC] [$]"). done. 
    Qed.

    (* TODO: make iMod work with cwp instead *)
    Lemma cwp_elim_bupd (e: expr Λ) (Φ: val Λ -> iProp Σ) (s: stuckness) (ε__wp ε__lift: coPset) (τ: locale Λ) (ρ: fmrole M) (P: iProp Σ):
      ⊢ (P -∗ cwp e Φ s ε__wp ε__lift τ ρ) -∗ (|==> P) -∗ cwp e Φ s ε__wp ε__lift τ ρ.
    Proof.
      iIntros "IMPL P". iMod "P" as "P".
      by iApply "IMPL".
    Qed.

  End CWP.

End ModelPlug.


Lemma cwp_convert
  `{EM: ExecutionModel Λ M__glob}
  `{!irisG Λ M__glob Σ}
  `{eGS: em_GS Σ}
   {M M': FairModel}
   {msi: fmstate M -> iProp Σ} {msi': fmstate M' -> iProp Σ}
   {lr lr'}
   (CWP := @cwp _ _ EM _ eGS _ msi lr _)
   (CWP' := @cwp _ _ EM _ eGS _ msi' lr' _)
   (RL := @role_lift _ _ EM Σ eGS _ msi lr iris_invGS)
   (RL' := @role_lift _ _ EM Σ eGS _ msi' lr' iris_invGS)
   (e: expr Λ) τ (Φ Φ': val Λ -> iProp Σ) s ε__wp ε__lift ε__lift' ρ ρ':
      ⊢ CWP' e Φ' s ε__wp ε__lift' τ ρ' -∗
        (∀ LC, LC -∗ RL ε__lift τ ρ LC -∗ ∃ LC', LC' ∗ RL' ε__lift' τ ρ' LC' ∗ (∀ v,  Φ' v ∗ LC' -∗ Φ v ∗ LC)) -∗
        CWP e Φ s ε__wp ε__lift τ ρ.
Proof.
  iIntros "CWP' CONV".
  rewrite /CWP /cwp. iIntros (LC) "LC RL".
  iSpecialize ("CONV" $! _ with "LC RL").
  iDestruct "CONV" as (LC') "(LC' & RL' & CONV)".
  iSpecialize ("CWP'" with "LC' RL'").
  iApply (wp_strong_mono with "CWP'").
  1, 2: reflexivity.
  iIntros. iModIntro. by iApply "CONV".
Qed. 

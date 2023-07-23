From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import heap_lang_defs. 
From trillium.fairness Require Import fairness fuel.
From trillium.fairness Require Import partial_ownership.

Section PartialModelPredicates.
(* Context `{LM: LiveModel Λ M}. *)
(* Context {fG: fairnessGS LM Σ}. *)
  Context `{iLM: LiveModel heap_lang iM}. 
  Context `{EM: ExecutionModel M}.
  Context `{eGS: em_GS Σ}. 
  (* Context {ifG: fairnessGS iLM Σ}. *)
  Context `{invGS_gen HasNoLc Σ}.
  Context {PMPP: @PartialModelPredicatesPre heap_lang _ _ Σ iM}. 

(* TODO: it might make sense to extract LM_step_lifting_def from PMP
   since this is the only premise that mentions heap_lang *)
  Let Λ := heap_lang. 

  Let LM_step_lifting_def: iProp Σ := 
      ∀ σ1 δ1, em_msi σ1 δ1 (em_GS0 := eGS) →
               ∃ δ1',
                 (* model_state_interp σ1 δ1' (LM := iLM) *)
                 partial_msi σ1 δ1'
                   ∗
             ∀ (σ2: cfg heap_lang) δ2' oζ ℓ',
               ⌜ valid_evolution_step oζ σ2 δ1' ℓ' δ2' (LM := iLM)⌝ →
               (* model_state_interp σ2 δ2' (LM := iLM) *)
               partial_msi σ2 δ2'
               →
               ∃ δ2 ℓ, em_msi σ2 δ2 (em_GS0 := eGS) ∗
                       ⌜ em_valid_evolution_step oζ σ2 δ1 ℓ δ2⌝.

    
  
  Let update_no_step_enough_fuel_step_def 
    (c1 c2 : cfg Λ) (δ1': iLM) (fs : gmap (fmrole iM) nat) (ζ : locale Λ)
    `(dom fs ≠ ∅)
    `(locale_step c1 (Some ζ) c2) : iProp Σ :=
        (
        has_fuels ζ (S <$> fs) -∗
           partial_msi c1 δ1' ==∗
           ∃ (δ2' : iLM) (ℓ' : mlabel iLM),
             ⌜labels_match (Some ζ) ℓ' (LM := iLM) ∧
               (* valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2) (auxtr :tr[ ℓ ]: δ2)⌝ *)
               valid_evolution_step (Some ζ) c2 δ1' ℓ' δ2' (LM := iLM) ⌝
                  ∗
             has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) ∗
             partial_msi c2 δ2')%I.

  
  Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).
  
  Let update_fork_split_step_def (R1 R2: gset (fmrole iM)) tp1 tp2
        (fs: gmap (fmrole iM) nat) (δ1': iLM)
        ζ efork σ1 σ2
         `(R1 ## R2)
         `(fs ≠ ∅)
         `(R1 ∪ R2 = dom fs)
         (* `(trace_last extr = (tp1, σ1)) *)
         `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
         `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)): iProp Σ :=
    (* has_fuels_S ζ fs -∗ *)
    has_fuels ζ (S <$> fs) -∗
      partial_msi (tp1, σ1) δ1' ==∗
      ∃ δ2' ℓ', has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗
            has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗ 
               (* frag_mapping_is {[ locale_of tp1 efork := ∅ ]} (LM := LM) *)
               em_thread_post (locale_of tp1 efork) (em_GS0 := eGS)
) ∗
            partial_msi (tp2, σ2) δ2' ∧
            (* ⌜valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[Silent_step ζ]: δ2)⌝). *)
            ⌜ valid_evolution_step (Some ζ) (tp2, σ2) δ1' ℓ' δ2' (LM := iLM)⌝. 


    Let update_step_still_alive_step_def
      tp1 tp2 σ1 σ2
      (s1 s2: iM)
      (fs1 fs2: gmap (fmrole iM) nat)
      ρ (δ1': iLM) ζ fr1 fr_stash
      (Einvs: coPset)
    `((live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1)
    `(fr_stash ⊆ dom fs1)
    `((live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅)
    `(dom fs2 ∩ fr_stash = ∅)
    (* `(trace_last extr = (tp1, σ1)) *)
    (* `(trace_last auxtr = δ1) *)
    `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
    `(fmtrans _ s1 (Some ρ) s2)
     `(valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM))
      : iProp Σ :=
    ( has_fuels ζ fs1 -∗ partial_model_is s1 -∗ partial_msi (tp1, σ1) δ1' -∗
    partial_free_roles_are fr1
    ={ Einvs }=∗
    ∃ (δ2': iLM) ℓ',
      ⌜
       labels_match (Some ζ) ℓ' (LM := iLM) ∧
       (* valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2) *)
        valid_evolution_step (Some ζ) (tp2, σ2) δ1' ℓ' δ2' (LM := iLM)
         ⌝ ∗
      has_fuels ζ fs2 ∗ partial_model_is s2 ∗ partial_msi (tp2, σ2) δ2' ∗
      partial_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash)). 

    Let partial_free_roles_fuels_disj_def n δ fr fs tid: iProp Σ :=
        partial_msi n δ -∗ partial_free_roles_are fr -∗ has_fuels tid fs -∗ ⌜ fr ## dom fs ⌝.

    Let PMP_def (Einvs: coPset): iProp Σ := □ (
          (∀ extr auxtr c2 fs ζ NE STEP, update_no_step_enough_fuel_step_def extr auxtr c2 fs ζ NE STEP) ∗         
          (∀ R1 R2 tp1 tp2 fs δ1' ζ efork σ1 σ2 DISJ NE DOM STEP POOL, update_fork_split_step_def R1 R2 tp1 tp2 fs δ1' ζ efork σ1 σ2 DISJ NE DOM STEP POOL) ∗ 
          (∀ tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1' ζ fr1 fr_stash
             LR STASH NSL NOS2 STEP STEP' VFM,
              update_step_still_alive_step_def tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1' ζ fr1 fr_stash Einvs LR STASH NSL NOS2 STEP STEP' VFM) ∗
          (∀ n δ fr fs tid, partial_free_roles_fuels_disj_def n δ fr fs tid) ∗
          LM_step_lifting_def
).  

    Definition PartialModelPredicates Einvs: iProp Σ := PMP_def Einvs. 

    Lemma Build_PartialModelPredicates Einvs: PMP_def Einvs ⊢ PartialModelPredicates Einvs.
    Proof. done. Qed. 

    Global Instance PMP_pers: forall Einvs, Persistent (PartialModelPredicates Einvs). 
    Proof. apply _. Qed. 
    
    (* Doing this _def indirection to provide the "PMP -∗ (property)" lemmas
       while gathering them in one iProp to ease the constructions,
       and make PMP opaque, since its unfold takes too much space *)

    Lemma LM_step_lifting {Einvs}: 
      PartialModelPredicates Einvs ⊢ LM_step_lifting_def. 
    Proof. by iIntros "(?&?&?&?&?)". Qed.
    Lemma update_no_step_enough_fuel_step {Einvs} extr auxtr c2 fs ζ NE STEP: 
      PartialModelPredicates Einvs ⊢ update_no_step_enough_fuel_step_def extr auxtr c2 fs ζ NE STEP. 
    Proof. by iIntros "(?&?&?&?&?)". Qed.
    Lemma update_fork_split_step {Einvs} R1 R2 tp1 tp2 fs δ1' ζ efork σ1 σ2 DISJ NE DOM STEP POOL: 
      PartialModelPredicates Einvs ⊢ update_fork_split_step_def R1 R2 tp1 tp2 fs δ1' ζ efork σ1 σ2 DISJ NE DOM STEP POOL. 
    Proof. by iIntros "(?&?&?&?&?)". Qed.
    Lemma update_step_still_alive_step {Einvs} tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1' ζ fr1 fr_stash LR STASH NSL NOS2 STEP STEP' VFM:
      PartialModelPredicates Einvs ⊢ update_step_still_alive_step_def tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1' ζ fr1 fr_stash Einvs LR STASH NSL NOS2 STEP STEP' VFM.
    Proof. by iIntros "(?&?&?&?&?)". Qed.
    Lemma partial_free_roles_fuels_disj {Einvs} n δ fr fs tid:
      PartialModelPredicates Einvs ⊢ partial_free_roles_fuels_disj_def n δ fr fs tid.
    Proof. by iIntros "(?&?&?&?&?)". Qed.

    Global Opaque PartialModelPredicates.

    Lemma update_no_step_enough_fuel {Einvs} (extr : execution_trace Λ) 
      (auxtr : auxiliary_trace M) 
      (c2 : cfg Λ) (fs : gmap (fmrole iM) nat) (ζ : locale Λ)
      `(dom fs ≠ ∅)
      `(locale_step (trace_last extr) (Some ζ) c2) :
      PartialModelPredicates Einvs  ⊢ (
          has_fuels ζ (S <$> fs) -∗
           em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ==∗
           ∃ (δ2 : M) (ℓ : mlabel M),
             ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
               (auxtr :tr[ ℓ ]: δ2)⌝ ∗
               has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) ∗
               em_msi c2 δ2 (em_GS0 := eGS))%I.
    Proof using. 
      iIntros "#PMP FUELS MSI". 
      iDestruct (LM_step_lifting with "PMP MSI") as (?) "[MSI' LIFT]". 
      unshelve iMod (update_no_step_enough_fuel_step with "PMP FUELS MSI'") as (?? [??]) "[FUELS MSI']"; eauto.
      iDestruct ("LIFT" with "[] [MSI']") as (??) "(MSI & %EV)"; eauto.
      iModIntro. do 2 iExists _. iFrame. by destruct c2. 
    Qed. 
   
    Lemma update_fork_split {Einvs} (R1 R2: gset (fmrole iM)) tp1 tp2
       (fs: gmap (fmrole iM) nat)
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace M) ζ efork σ1 σ2
          `(R1 ## R2)
          `(fs ≠ ∅)
          `(R1 ∪ R2 = dom fs)
         `(trace_last extr = (tp1, σ1))
          `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
          `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)):
       PartialModelPredicates Einvs ⊢ (
     has_fuels ζ (S <$> fs) -∗
      em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ==∗
      ∃ δ2 ℓ, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗
             has_fuels ζ (fs ⇂ R1) ∗
             (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗
                (* frag_mapping_is {[ locale_of tp1 efork := ∅ ]} (LM := LM) *)
                em_thread_post (locale_of tp1 efork) (em_GS0 := eGS)
) ∗
            em_msi (tp2, σ2) δ2 (em_GS0 := eGS) ∧ ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝).
    Proof.
      iIntros "#PMP FUELS MSI". rewrite H3. 
      iDestruct (LM_step_lifting with "PMP MSI") as (?) "[MSI' LIFT]". 
      unshelve iMod (update_fork_split_step with "PMP FUELS MSI'") as (??) "(?&?&?&MSI'&%)". 
      6: by apply H0.
      all: eauto. 
      iDestruct ("LIFT" with "[] [MSI']") as (??) "(MSI & %EV)"; eauto.
      iModIntro.
      do 2 iExists _. iFrame. done.
    Qed. 
 
    Lemma update_step_still_alive
      (extr : execution_trace Λ)
      (auxtr: auxiliary_trace M)
       tp1 tp2 σ1 σ2
       (s1 s2: iM)
       (fs1 fs2: gmap (fmrole iM) nat)
      ρ (δ1 : M) ζ fr1 fr_stash
       (Einvs: coPset)
     `((live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1)
     `(fr_stash ⊆ dom fs1)
     `((live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅)
     `(dom fs2 ∩ fr_stash = ∅)
    `(trace_last extr = (tp1, σ1))
    `(trace_last auxtr = δ1)
     `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
     `(fmtrans _ s1 (Some ρ) s2)
      `(valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM)):
  PartialModelPredicates Einvs ⊢ 
    ( has_fuels ζ fs1 -∗ partial_model_is s1 -∗ em_msi (tp1, σ1) δ1 (em_GS0 := eGS) -∗
     partial_free_roles_are fr1
     ={ Einvs }=∗
    ∃ (δ2: M) ℓ,
      ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝ ∗
      has_fuels ζ fs2 ∗ partial_model_is s2 ∗ em_msi (tp2, σ2) δ2 (em_GS0 := eGS)∗
       partial_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪
                                   fr_stash)).    
    Proof using. 
      iIntros "#PMP FUELS ST MSI FR".
      iDestruct (LM_step_lifting with "PMP MSI") as (?) "[MSI' LIFT]". 
      unshelve iMod (update_step_still_alive_step with "PMP [$] [$] [$] [$]") as (??) "([%%]&?&?&MSI'&?)"; eauto.
      iDestruct ("LIFT" with "[] [MSI']") as (??) "(MSI & %EV)"; eauto.
      iModIntro.
      do 2 iExists _. iFrame. iPureIntro.
      simpl. by rewrite H5.
    Qed.

End PartialModelPredicates.

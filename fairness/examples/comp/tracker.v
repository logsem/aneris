From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth numbers gset csum. 
From iris.proofmode Require Import tactics.


Section TrackerRA.

  Definition trackerRA: ucmra := excl_authR boolO. 
  
  Definition tr_tracked: bool := true.
  Definition tr_free: bool := false.

  (***********)
  
  Context `{inG Σ trackerRA}.   
  
  Definition tracked (γ: gname) (P: iProp Σ): iProp Σ :=
    own γ (●E tr_tracked) ∗ P ∨ own γ (●E tr_free).

  Lemma init_tracker (P: iProp Σ): 
    ⊢ (|==> ∃ γ, tracked γ P ∗ own γ (◯E tr_free))%I.
  Proof.
    iStartProof. 
    iMod (own_alloc (●E tr_free  ⋅ ◯E tr_free)) as (γ) "[AUTH FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    iModIntro. iExists _. iFrame.
  Qed. 

  Lemma start_tracking γ (P: iProp Σ):
    ⊢ (own γ (◯E tr_free) ∗ P ∗ tracked γ P ==∗ own γ (◯E tr_tracked) ∗ tracked γ P)%I.
  Proof.
    iIntros "(FRAG & P & [[AUTH ?] | AUTH])".
    { iDestruct (own_op with "[FRAG AUTH]") as "O"; [by iFrame| ].
      iDestruct (own_valid with "O") as "%V".      
      eapply excl_auth_agree in V. done. } 

    iMod (own_update with "[AUTH FRAG]") as "OWN". 
    { eapply excl_auth_update. }
    { iApply own_op. iFrame. }
    iDestruct "OWN" as "[AUTH FRAG]". 
    
    iModIntro. iFrame. iLeft. iFrame.
  Qed. 

  Lemma stop_tracking γ (P: iProp Σ):
    ⊢ (own γ (◯E tr_tracked) ∗ tracked γ P ==∗ own γ (◯E tr_free) ∗ P ∗ tracked γ P)%I.
  Proof.
    iIntros "(FRAG & [[AUTH ?] | AUTH])".
    2: { iDestruct (own_op with "[FRAG AUTH]") as "O"; [by iFrame| ].
         iDestruct (own_valid with "O") as "%V".      
         eapply excl_auth_agree in V. done. }

    iMod (own_update with "[AUTH FRAG]") as "OWN". 
    { eapply excl_auth_update. }
    { iApply own_op. iFrame. }
    iDestruct "OWN" as "[AUTH FRAG]". 
    
    iModIntro. iFrame.
  Qed. 
  

End TrackerRA.

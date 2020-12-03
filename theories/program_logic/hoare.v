From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export viewshifts.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Definition ht `{!irisG Λ Σ} (s : stuckness) (E : coPset) (P : iProp Σ)
    (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ :=
  (□ (P -∗ WP e @ s; E {{ Φ }}))%I.
Instance: Params (@ht) 5 := {}.

Notation "{{ P } } e @ s ; E {{ Φ } }" := (ht s E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  s ;  E  {{  Φ  } }") : stdpp_scope.
Notation "{{ P } } e @ E {{ Φ } }" := (ht NotStuck E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : stdpp_scope.
Notation "{{ P } } e @ E ? {{ Φ } }" := (ht MaybeStuck E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  ? {{  Φ  } }") : stdpp_scope.
Notation "{{ P } } e {{ Φ } }" := (ht NotStuck ⊤ P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : stdpp_scope.
Notation "{{ P } } e ? {{ Φ } }" := (ht MaybeStuck ⊤ P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  ? {{  Φ  } }") : stdpp_scope.

Notation "{{ P } } e @ s ; E {{ v , Q } }" := (ht s E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  s ;  E  {{  v ,  Q  } }") : stdpp_scope.
Notation "{{ P } } e @ E {{ v , Q } }" := (ht NotStuck E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  {{  v ,  Q  } }") : stdpp_scope.
Notation "{{ P } } e @ E ? {{ v , Q } }" := (ht MaybeStuck E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  ? {{  v ,  Q  } }") : stdpp_scope.
Notation "{{ P } } e {{ v , Q } }" := (ht NotStuck ⊤ P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.
Notation "{{ P } } e ? {{ v , Q } }" := (ht MaybeStuck ⊤ P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  ? {{  v ,  Q  } }") : stdpp_scope.

Section hoare.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ht_ne s E n :
  Proper (dist n ==> eq ==> pointwise_relation _ (dist n) ==> dist n) (ht s E).
Proof. solve_proper. Qed.
Global Instance ht_proper s E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (ht s E).
Proof. solve_proper. Qed.
Lemma ht_mono s E P P' Φ Φ' e :
  (P ⊢ P') → (∀ v, Φ' v ⊢ Φ v) → {{ P' }} e @ s; E {{ Φ' }} ⊢ {{ P }} e @ s; E {{ Φ }}.
Proof. by intros; apply affinely_mono, persistently_mono, wand_mono, wp_mono. Qed.
Lemma ht_stuck_mono s1 s2 E P Φ e :
  s1 ⊑ s2 → {{ P }} e @ s1; E {{ Φ }} ⊢ {{ P }} e @ s2; E {{ Φ }}.
Proof. by intros; apply affinely_mono, persistently_mono, wand_mono, wp_stuck_mono. Qed.
Global Instance ht_mono' s E :
  Proper (flip (⊢) ==> eq ==> pointwise_relation _ (⊢) ==> (⊢)) (ht s E).
Proof. solve_proper. Qed.

Lemma ht_alt s E P Φ e : (P ⊢ WP e @ s; E {{ Φ }}) → ⊢ {{ P }} e @ s; E {{ Φ }}.
Proof. iIntros (Hwp) "!> HP". by iApply Hwp. Qed.

Lemma ht_val s E v : ⊢ {{ True }} of_val v @ s; E {{ v', ⌜v = v'⌝ }}.
Proof. iIntros "!> _". by iApply wp_value'. Qed.

Lemma ht_vs s E P P' Φ Φ' e :
  (P ={E}=> P') ∧ {{ P' }} e @ s; E {{ Φ' }} ∧ (∀ v, Φ' v ={E}=> Φ v)
  ⊢ {{ P }} e @ s; E {{ Φ }}.
Proof.
  iIntros "(#Hvs & #Hwp & #HΦ) !> HP". iMod ("Hvs" with "HP") as "HP".
  iApply wp_fupd. iApply (wp_wand with "(Hwp HP)").
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma ht_atomic s E1 E2 P P' Φ Φ' e `{!Atomic (stuckness_to_atomicity s) e} :
  (P ={E1,E2}=> P') ∧ {{ P' }} e @ s; E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @ s; E1 {{ Φ }}.
Proof.
  iIntros "(#Hvs & #Hwp & #HΦ) !> HP". iApply (wp_atomic _ _ E2); auto.
  iMod ("Hvs" with "HP") as "HP". iModIntro.
  iApply (wp_wand with "(Hwp HP)").
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma ht_bind `{!LanguageCtx K} s E P Φ Φ' e :
  {{ P }} e @ s; E {{ Φ }} ∧ (∀ v, {{ Φ v }} K (of_val v) @ s; E {{ Φ' }})
  ⊢ {{ P }} K e @ s; E {{ Φ' }}.
Proof.
  iIntros "[#Hwpe #HwpK] !> HP". iApply wp_bind.
  iApply (wp_wand with "(Hwpe HP)").
  iIntros (v) "Hv". by iApply "HwpK".
Qed.

Lemma ht_stuck_weaken s E P Φ e :
  {{ P }} e @ s; E {{ Φ }} ⊢ {{ P }} e @ E ?{{ Φ }}.
Proof.
  by iIntros "#Hwp !> ?"; iApply wp_stuck_weaken; iApply "Hwp".
Qed.

Lemma ht_mask_weaken s E1 E2 P Φ e :
  E1 ⊆ E2 → {{ P }} e @ s; E1 {{ Φ }} ⊢ {{ P }} e @ s; E2 {{ Φ }}.
Proof.
  iIntros (?) "#Hwp !> HP". iApply (wp_mask_mono _ E1 E2); try done.
  by iApply "Hwp".
Qed.

Lemma ht_frame_l s E P Φ R e :
  {{ P }} e @ s; E {{ Φ }} ⊢ {{ R ∗ P }} e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "#Hwp !> [$ HP]". by iApply "Hwp". Qed.

Lemma ht_frame_r s E P Φ R e :
  {{ P }} e @ s; E {{ Φ }} ⊢ {{ P ∗ R }} e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "#Hwp !> [HP $]". by iApply "Hwp". Qed.

Lemma ht_frame_step_l s E1 E2 P R1 R2 e Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @ s; E2 {{ Φ }}
  ⊢ {{ R1 ∗ P }} e @ s; E1 {{ λ v, R2 ∗ Φ v }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !> [HR HP]".
  iApply (wp_frame_step_l _ E1 E2); try done.
  iSplitL "HR"; [by iApply "Hvs"|by iApply "Hwp"].
Qed.

Lemma ht_frame_step_r s E1 E2 P R1 R2 e Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @ s; E2 {{ Φ }}
  ⊢ {{ P ∗ R1 }} e @ s; E1 {{ λ v, Φ v ∗ R2 }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !> [HP HR]".
  iApply (wp_frame_step_r _ E1 E2); try done.
  iSplitR "HR"; [by iApply "Hwp"|by iApply "Hvs"].
Qed.

Lemma ht_frame_step_l' s E P R e Φ :
  TCEq (to_val e) None →
  {{ P }} e @ s; E {{ Φ }} ⊢ {{ ▷ R ∗ P }} e @ s; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "#Hwp !> [HR HP]".
  iApply wp_frame_step_l'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma ht_frame_step_r' s E P Φ R e :
  TCEq (to_val e) None →
  {{ P }} e @ s; E {{ Φ }} ⊢ {{ P ∗ ▷ R }} e @ s; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "#Hwp !> [HP HR]".
  iApply wp_frame_step_r'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma ht_exists (T : Type) s E (P : T → iProp Σ) Φ e :
  (∀ x, {{ P x }} e @ s; E {{ Φ }}) ⊢ {{ ∃ x, P x }} e @ s; E {{ Φ }}.
Proof. iIntros "#HT !> HP". iDestruct "HP" as (x) "HP". by iApply "HT". Qed.

End hoare.

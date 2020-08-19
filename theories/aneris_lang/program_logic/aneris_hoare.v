From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export viewshifts.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
Set Default Proof Using "Type".

Import Network.

Definition aht `{!anerisG Σ} (ip : ip_address) (E : coPset) (P : iProp Σ)
    (e : expr) (Φ : val → iProp Σ) : iProp Σ :=
  (□ (P -∗ WP e @[ip] E {{ Φ }}))%I.
Instance: Params (@aht) 5 := {}.

Notation "{{ P } } e '@[' ip ] E {{ Φ } }" := (aht ip E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @[ ip ]  E  {{  Φ  } }") : stdpp_scope.

Notation "{{ P } } e '@[' ip ] E {{ v , Q } }" := (aht ip E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @[ ip ]  E  {{  v ,  Q  } }") : stdpp_scope.

Section hoare.
Context `{!anerisG Σ}.
Implicit Types ip : ip_address.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types v : val.
Import uPred.

Global Instance aht_ne ip E n :
  Proper (dist n ==> eq ==> pointwise_relation _ (dist n) ==> dist n) (aht ip E).
Proof. solve_proper. Qed.
Global Instance aht_proper ip E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (aht ip E).
Proof. solve_proper. Qed.
Lemma aht_mono ip E P P' Φ Φ' e :
  (P ⊢ P') →
  (∀ v, Φ' v ⊢ Φ v) →
  {{ P' }} e @[ip] E {{ Φ' }} ⊢ {{ P }} e @[ip] E {{ Φ }}.
Proof.
  intros; apply affinely_mono, persistently_mono, wand_mono, aneris_wp_mono; done.
Qed.
Global Instance aht_mono' ip E :
  Proper (flip (⊢) ==> eq ==> pointwise_relation _ (⊢) ==> (⊢)) (aht ip E).
Proof. solve_proper. Qed.

Lemma aht_alt ip E P Φ e :
  (P ⊢ WP e @ ip; E {{ Φ }}) → ⊢ {{ P }} e @[ip] E {{ Φ }}.
Proof. iIntros (Hwp) "!> HP". by iApply Hwp. Qed.

Lemma aht_val ip E v :
  ⊢ {{ True }} of_val v @[ip] E {{ v', ⌜v = v'⌝ }}.
Proof. iIntros "!> _". by iApply aneris_wp_value'. Qed.

Lemma aht_vs ip E P P' Φ Φ' e :
  (P ={E}=> P') ∧ {{ P' }} e @[ip] E {{ Φ' }} ∧ (∀ v, Φ' v ={E}=> Φ v)
  ⊢ {{ P }} e @[ip] E {{ Φ }}.
Proof.
  iIntros "(#Hvs & #Hwp & #HΦ) !> HP". iMod ("Hvs" with "HP") as "HP".
  iApply aneris_wp_fupd. iApply (aneris_wp_wand with "(Hwp HP)").
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma aht_atomic ip E1 E2 P P' Φ Φ' e `{!Atomic WeaklyAtomic (mkExpr ip e)} :
  (P ={E1,E2}=> P') ∧ {{ P' }} e @[ip] E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @[ip] E1 {{ Φ }}.
Proof.
  iIntros "(#Hvs & #Hwp & #HΦ) !> HP". iApply (aneris_wp_atomic _ _ E2); auto.
  iMod ("Hvs" with "HP") as "HP". iModIntro.
  iApply (aneris_wp_wand with "(Hwp HP)").
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma aht_bind K ip E P Φ Φ' e :
  {{ P }} e @[ip] E {{ Φ }} ∧ (∀ v, {{ Φ v }} fill K (of_val v) @[ip] E {{ Φ' }})
  ⊢ {{ P }} fill K e @[ip] E {{ Φ' }}.
Proof.
  iIntros "[#Hwpe #HwpK] !> HP". iApply aneris_wp_bind.
  iApply (aneris_wp_wand with "(Hwpe HP)").
  iIntros (v) "Hv". by iApply "HwpK".
Qed.

Lemma aht_mask_weaken ip E1 E2 P Φ e :
  E1 ⊆ E2 → {{ P }} e @[ip] E1 {{ Φ }} ⊢ {{ P }} e @[ip] E2 {{ Φ }}.
Proof.
  iIntros (?) "#Hwp !> HP". iApply (aneris_wp_mask_mono _ E1 E2); try done.
  by iApply "Hwp".
Qed.

Lemma aht_frame_l ip E P Φ R e :
  {{ P }} e @[ip] E {{ Φ }} ⊢ {{ R ∗ P }} e @[ip] E {{ v, R ∗ Φ v }}.
Proof. iIntros "#Hwp !> [$ HP]". by iApply "Hwp". Qed.

Lemma aht_frame_r ip E P Φ R e :
  {{ P }} e @[ip] E {{ Φ }} ⊢ {{ P ∗ R }} e @[ip] E {{ v, Φ v ∗ R }}.
Proof. iIntros "#Hwp !> [HP $]". by iApply "Hwp". Qed.

Lemma aht_frame_step_l ip E1 E2 P R1 R2 e Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @[ip] E2 {{ Φ }}
  ⊢ {{ R1 ∗ P }} e @[ip] E1 {{ λ v, R2 ∗ Φ v }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !> [HR HP]".
  iApply (aneris_wp_frame_step_l _ E1 E2); try done.
  iSplitL "HR"; [by iApply "Hvs"|by iApply "Hwp"].
Qed.

Lemma aht_frame_step_r ip E1 E2 P R1 R2 e Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @[ip] E2 {{ Φ }}
  ⊢ {{ P ∗ R1 }} e @[ip] E1 {{ λ v, Φ v ∗ R2 }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !> [HP HR]".
  iApply (aneris_wp_frame_step_r _ E1 E2); try done.
  iSplitR "HR"; [by iApply "Hwp"|by iApply "Hvs"].
Qed.

Lemma aht_frame_step_l' ip E P R e Φ :
  TCEq (to_val e) None →
  {{ P }} e @[ip] E {{ Φ }} ⊢ {{ ▷ R ∗ P }} e @[ip] E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "#Hwp !> [HR HP]".
  iApply aneris_wp_frame_step_l'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma aht_frame_step_r' ip E P Φ R e :
  TCEq (to_val e) None →
  {{ P }} e @[ip] E {{ Φ }} ⊢ {{ P ∗ ▷ R }} e @[ip] E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "#Hwp !> [HP HR]".
  iApply aneris_wp_frame_step_r'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma aht_exists (T : Type) ip E (P : T → iProp Σ) Φ e :
  (∀ x, {{ P x }} e @[ip] E {{ Φ }}) ⊢ {{ ∃ x, P x }} e @[ip] E {{ Φ }}.
Proof. iIntros "#HT !> HP". iDestruct "HP" as (x) "HP". by iApply "HT". Qed.

End hoare.

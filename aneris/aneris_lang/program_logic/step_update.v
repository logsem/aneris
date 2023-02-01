From iris.proofmode Require Import tactics.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Section with_Σ.
  Context `{!anerisG Mdl Σ}.

  (* TODO: Move/Rename these *)
  Lemma step_fupdN_frame_l' Eo Ei n (R Q : iProp Σ) :
    (▷^n R ∗ |={Eo}[Ei]▷=>^n Q) -∗ |={Eo}[Ei]▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]".
    iApply IH. by iFrame.
  Qed.

  Lemma step_fupdN_empty_sep n (R Q : iProp Σ) :
    (|={∅}▷=>^n R) ∗ (|={∅}▷=>^n Q) -∗ |={∅}▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]". iApply IH.
    iMod "HR". iMod "HQ". iIntros "!>!>". iMod "HR". iMod "HQ". by iFrame.
  Qed.

  Definition step_get E1 E2 P : iProp Σ :=
    ∀ n, steps_auth n ={E1,E2}=∗ steps_auth n ∗ (P n).

  Notation "|~{ E1 , E2 }~| P" := (step_get E1 E2 (λ _, |={E2,E1}=> P))%I (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~|  '/' P ']'").
  Notation "|~{ E }~| P" := (|~{E,∅}~| P) (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
  Notation "|~~| P" := (|~{∅}~| P) (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

  Lemma aneris_wp_step_get ip E e P Φ :
    TCEq (to_val e) None →
    (|~{E}~| P) -∗
    (P -∗ WP e @[ip] E {{ Φ }}) -∗
    WP e @[ip] E {{ Φ }}.
  Proof.
    iIntros (Hval) "HP Hwp".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros (tid) "Hip".
    rewrite !wp_unfold /wp_pre /= /aneris_to_val /= Hval.
    iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe)
            "(?&?&?&?&Hauth)".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod "HP".
    iDestruct ("Hwp" with "HP Hip") as "Hwp".
    rewrite !wp_unfold /wp_pre /= /aneris_to_val /= Hval.
    iMod ("Hwp" with "[//] [//] [//] [$]") as "[% H]".
    iModIntro.
    iSplit; [done|].
    iIntros (e2 σ2 efs Hstep). simpl.
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    iMod "H" as "H". iIntros "!>".
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "H". iMod "H" as (δ2 ℓ) "((?&?&?&?&Hauth) & H & Hefs)".
    iModIntro.
    iExists δ2, ℓ.
    iFrame.
  Qed.

  Lemma step_get_impl E P Q :
    (|~{E}~| P) -∗ (P -∗ |~{E}~| Q) -∗ |~{E}~| Q.
  Proof.
    iIntros "HP HPQ".
    iIntros (n) "Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod "HP". by iMod ("HPQ" with "HP Hauth") as "HPQ".
  Qed.

  Lemma step_get_intro E P :
    P -∗ |~{E}~| P.
  Proof.
    iIntros "HP" (n) "Hauth". iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". iFrame. done.
  Qed.

  Lemma step_get_lb_get E :
    ⊢ |~{E}~| steps_lb 0.
  Proof.
    iIntros (m) "Hauth".
    iDestruct (steps_lb_get with "Hauth") as "#Hlb".
    iDestruct (steps_lb_le with "Hlb") as "$"; [lia|].
    iFrame. iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iMod "Hclose". by iModIntro.
  Qed.

  Lemma aneris_wp_lb_get ip E e Φ :
    TCEq (to_val e) None →
    (steps_lb 0 -∗ WP e @[ip] E {{ v, Φ v }}) -∗
    WP e @[ip] E {{ Φ }}.
  Proof.
    iIntros (Hval) "Hwp".
    iApply (aneris_wp_step_get); [|done]. iApply step_get_lb_get.
  Qed.

  Definition step_update E1 E2 P : iProp Σ :=
    step_get E1 E2 (λ n, (|={∅}▷=>^(S n)
                                   (steps_auth (S n) ={E2,E1}=∗
                                    steps_auth (S n) ∗ P)))%I.

  Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
  Notation "|~{ E }~> P" := (step_update E ∅ P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
  Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

  Lemma step_get_step_update E1 E2 P Q :
    (|~{E1}~| P) -∗
    (P -∗ |~{E1,E2}~> Q) -∗
    |~{E1,E2}~> Q.
  Proof.
    iIntros "HP HPQ".
    iIntros (n) "Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod "HP".
    iMod ("HPQ" with "HP Hauth") as "[Hauth HPQ]". by iFrame.
  Qed.

  Lemma step_update_frame E1 E2 Ef P :
    E2 ⊆ E1 → E1 ## Ef →
    (|~{E1,E2}~> P) -∗
    (|~{E1 ∪ Ef,E2 ∪ Ef}~> P).
  Proof.
    iIntros (Hle Hidjs) "Hstep".
    iIntros (n) "Hauth".
    iDestruct ("Hstep" with "Hauth") as "Hstep".
    iDestruct (fupd_mask_frame_r E1 E2 Ef with "Hstep") as "Hstep"; [done|].
    iMod "Hstep" as "[Hauth Hstep]".
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose".
    iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep Hauth".
    iDestruct ("Hstep" with "Hauth") as "Hstep".
    iMod "Hclose".
    iApply fupd_mask_frame_r; [set_solver|].
    iMod "Hstep".
    iModIntro. done.
  Qed.

  Lemma aneris_wp_step_update_strong ip E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|~{E1,E2}~> P) -∗
    WP e @[ip] E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (Hval HE) "Hstep Hwp".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros (tid) "Hip".
    iDestruct ("Hwp" with "Hip") as "Hwp".
    rewrite !wp_unfold /wp_pre /=.
    rewrite /aneris_to_val. simpl. rewrite Hval. simpl.
    iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe)
            "(?&?&?&?&Hauth)".
    iMod ("Hstep" with "Hauth") as "[Hauth Hstep]". simpl.
    iMod ("Hwp" with "[//] [//] [//] [$]") as "[% H]".
    iMod "Hstep".
    iModIntro.
    iSplit; [done|].
    iIntros (e2 σ2 efs Hstep). simpl.
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    iMod "H" as "H".
    iMod "Hstep".
    iIntros "!>".
    iAssert (|={∅}▷=>^(trace_length extr) _ ∗ _)%I with "[H Hstep]" as "H".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "[Hstep H]". iMod "H" as (δ2 ℓ) "((?&?&?&?&Hauth) & H & Hefs)".
    iMod ("Hstep" with "Hauth") as "[Hauth HP]".
    iModIntro.
    iExists δ2, ℓ.
    iFrame.
    iApply (wp_strong_mono with "H"); [done|done|..].
    iIntros (v) "H".
    iDestruct "H" as (w Hw) "H".
    iMod ("H" with "HP") as "H".
    iModIntro. iExists _. iFrame. done.
  Qed.

  Lemma aneris_wp_step_update ip E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|~{E1∖E2}~> P) -∗
    WP e @[ip] E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (Hval HE) "Hstep Hwp".
    iDestruct (step_update_frame (E1∖E2) ∅ (E2) with "Hstep") as "Hstep";
      [set_solver|set_solver|].
    replace (E1 ∖ E2 ∪ E2) with E1; last first.
    { rewrite difference_union_L. set_solver. }
    replace (∅ ∪ E2) with E2 by set_solver.
    by iApply (aneris_wp_step_update_strong with "Hstep").
  Qed.

  Lemma step_update_intro E1 E2 P :
    E2 ⊆ E1 → P -∗ |~{E1,E2}~> P.
  Proof.
    iIntros (HE) "HP". iIntros (n) "Hauth". iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". iFrame. iApply step_fupdN_intro; [set_solver|].
    iIntros "!>!> Hauth". iMod "Hclose". iFrame. done.
  Qed.

  Lemma step_update_frame_l E1 E2 P Q :
    (|~{E1,E2}~> P) -∗ (|={E1}=> Q) -∗ |~{E1,E2}~> (P ∗ Q).
  Proof.
    iIntros "HP HQ" (n) "Hauth".
    iMod "HQ". iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iApply (step_fupdN_wand with "HP").
    iIntros "HP Hauth". iMod ("HP" with "Hauth") as "[Hauth HP]". by iFrame.
  Qed.

  Lemma step_update_comm E1 E2 P Q :
    E1 ## E2 → (|~{E1}~> P) -∗ (|~{E2}~> Q) -∗ |~{E1 ∪ E2}~> P ∗ Q.
  Proof.
    iIntros (HE) "HP HQ". iIntros (n) "Hauth".
    iDestruct ("HP" with "Hauth") as "HP".
    iDestruct (fupd_mask_frame_r E1 ∅ E2 with "HP") as "HP"; [done|].
    iMod "HP" as "[Hauth HP]". rewrite union_empty_l_L.
    iMod ("HQ" with "Hauth") as "[Hauth HQ]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HQ". iIntros "!>!>". iMod "HP". iMod "HQ". iIntros "!>".
    iDestruct (step_fupdN_empty_sep with "[$HP $HQ]") as "HPQ".
    iApply (step_fupdN_wand with "[HPQ]"); first by iApply "HPQ".
    iIntros "[HP HQ] Hauth".
    iMod ("HQ" with "Hauth") as "[Hauth HQ]".
    iDestruct ("HP" with "Hauth") as "HP".
    iDestruct (fupd_mask_frame_r ∅ E1 E2 with "HP") as "HP"; [set_solver|].
    rewrite union_empty_l_L.
    iMod "HP". iFrame. done.
  Qed.

  Lemma step_update_impl E1 E2 P Q :
    (|~{E2,E2}~> P) -∗ (|~{E1,E2}~> P -∗ Q) -∗ |~{E1,E2}~> Q.
  Proof.
    iIntros "HP HPQ" (n) "Hauth".
    iMod ("HPQ" with "Hauth") as "[Hauth HPQ]".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HPQ". iIntros "!>!>". iMod "HP". iMod "HPQ". iIntros "!>".
    iAssert (|={∅}▷=>^n _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "H").
    iIntros "[HP HPQ] Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HPQ" with "Hauth") as "[Hauth HPQ]".
    iFrame. by iApply "HPQ".
  Qed.

  Lemma step_update_mono E1 E2 E3 P Q :
    E2 ⊆ E1 → (|~{E2,E3}~> P) -∗ (P ={E2,E1}=∗ Q) -∗ |~{E1,E3}~> Q.
  Proof.
    iIntros (Hle) "HP HPQ". iIntros (n) "Hauth".
    iApply fupd_mask_weaken; [done|]. iIntros "Hclose".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iAssert (|={∅}▷=>^n _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_frame_l. iFrame. iExact "HPQ". }
    iApply (step_fupdN_wand with "H").
    iIntros "[HPQ HP] Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HPQ" with "HP") as "HQ".
    by iFrame.
  Qed.

  Lemma step_update_open E1 E2 E3 P :
    (|={E1,E2}=> |~{E2,E3}~> (|={E2, E1}=> P)) -∗ |~{E1,E3}~> P.
  Proof.
    iIntros "Hstep" (n) "Hauth".
    iMod "Hstep". iMod ("Hstep" with "Hauth") as "[Hauth Hstep]".
    iIntros "!>". iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep Hauth".
    iMod ("Hstep" with "Hauth") as "[Hauth Hstep]".
    iMod "Hstep". iModIntro. by iFrame.
  Qed.

  Lemma step_update_lb_update E n :
    steps_lb n -∗ |~{E}~> (steps_lb (S n)).
  Proof.
    iIntros "Hlb" (m) "Hauth".
    iDestruct (steps_lb_valid with "Hauth Hlb") as %Hvalid.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iFrame=> /=.
    iIntros "!>!>!>".
    iApply step_fupdN_intro; [done|].
    iIntros "!> Hauth".
    iDestruct (steps_lb_get with "Hauth") as "#Hlb'".
    iDestruct (steps_lb_le _ (S n) with "Hlb'") as "Hlb''"; [lia|].
    iMod "Hclose". iFrame. done.
  Qed.

  Lemma step_update_lb_step E P n :
    steps_lb n -∗ (|={∅}▷=>^(S n) P) -∗ |~{E}~> P.
  Proof.
    iIntros "Hlb HP" (m) "Hauth".
    iDestruct (steps_lb_valid with "Hauth Hlb") as %Hvalid.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". iFrame.
    iApply (step_fupdN_le (S n)); [lia|done|].
    iApply (step_fupdN_wand with "HP").
    iIntros "HP Hauth".
    iMod "Hclose". by iFrame.
  Qed.

End with_Σ.

Notation "|~{ E1 , E2 }~| P" := (step_get E1 E2 (λ _, |={E2,E1}=> P))%I (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~|  '/' P ']'").
Notation "|~{ E }~| P" := (|~{E,∅}~| P) (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
Notation "|~~| P" := (|~{∅}~| P) (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
Notation "|~{ E }~> P" := (step_update E ∅ P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

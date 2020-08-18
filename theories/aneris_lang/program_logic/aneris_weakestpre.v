From iris.proofmode Require Import base tactics classes.
From aneris.aneris_lang Require Import basic_lifting.
From aneris.aneris_lang Require Export resources.
From aneris.aneris_lang Require Export network ground_lang.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Import weakestpre.
Set Default Proof Using "Type".

Import Network.

Definition aneris_wp_def `{!distG Σ} (ip : ip_address) (E : coPset)
           (e : expr) (Φ : val → iProp Σ) : iProp Σ:=
  (IsNode ip -∗ wp NotStuck E (mkExpr ip e) (λ v, ∃ w, ⌜v = mkVal ip w⌝ ∗ Φ w))%I.

Definition aneris_wp_aux `{!distG Σ} : seal (@aneris_wp_def Σ _).
Proof. by eexists. Qed.
Instance aneris_wp `{!distG Σ} : Wp ground_lang (iProp Σ) ip_address :=
  aneris_wp_aux.(unseal).
Definition aneris_wp_eq `{!distG Σ} : aneris_wp = @aneris_wp_def Σ _ :=
  aneris_wp_aux.(seal_eq).

Section aneris_wp.
Context `{!distG Σ}.
Implicit Types ip : ip_address.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

(* Weakest pre *)
Lemma aneris_wp_unfold ip E e Φ :
  WP e @ ip; E {{ Φ }} ⊣⊢ aneris_wp_def ip E e Φ.
Proof. rewrite /wp aneris_wp_eq //. Qed.

Global Instance aneris_wp_ne ip E e k :
  Proper (pointwise_relation _ (dist k) ==> dist k) (aneris_wp ip E e).
Proof.
  intros Φ1 Φ2 HΦ; rewrite aneris_wp_eq /aneris_wp_def; solve_proper.
Qed.
Global Instance aneris_wp_proper ip E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (aneris_wp ip E e).
Proof.
  intros Φ1 Φ2 HΦ; rewrite aneris_wp_eq /aneris_wp_def; solve_proper.
Qed.
Global Instance aneris_wp_contractive ip E e k :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later k) ==> dist k) (aneris_wp ip E e).
Proof.
  intros Htv Φ1 Φ2 HΦ; rewrite aneris_wp_eq /aneris_wp_def.
  f_equiv.
  apply wp_contractive.
  - rewrite /= /aneris_to_val Htv //.
  - destruct k; first done.
    solve_proper.
Qed.

Lemma aneris_wp_value' ip E Φ v : Φ v ⊢ WP of_val v @ ip; E {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite aneris_wp_unfold /aneris_wp_def.
  iIntros "Hin".
  iApply wp_value; eauto.
 Qed.
Lemma aneris_wp_value_inv' ip E Φ v :
  IsNode ip -∗ WP of_val v @ ip; E {{ Φ }} ={E}=∗ Φ v.
Proof.
  rewrite aneris_wp_unfold /aneris_wp_def.
  iIntros "Hin Hwp".
  iMod (wp_value_inv' _ _ _ (mkVal _ _) with "[Hin Hwp]") as "HΦ";
    first by iApply "Hwp".
  iDestruct "HΦ" as (w) "[% ?]"; simplify_eq; done.
 Qed.

Lemma aneris_wp_IsNode ip E Φ e :
  (IsNode ip -∗ WP e @ ip; E {{ Φ }}) ⊢ WP e @ ip; E {{ Φ }}.
Proof.
  rewrite aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp #Hin".
  iApply "Hwp"; done.
 Qed.

Lemma aneris_wp_strong_mono ip E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  WP e @ ip; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ ip; E2 {{ Ψ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (HE) "Hwp HΦ Hin".
  iApply (wp_strong_mono with "[Hin Hwp]"); [done|done|iApply "Hwp"; done|].
  iIntros (?); iDestruct 1 as (w) "[-> Hw]".
  iMod ("HΦ" with "Hw"); eauto.
Qed.

Lemma fupd_aneris_wp ip E e Φ :
  (|={E}=> WP e @ ip; E {{ Φ }}) ⊢ WP e @ ip; E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp Hin".
  iApply fupd_wp; iMod "Hwp"; iModIntro.
  iApply "Hwp"; done.
Qed.
Lemma aneris_wp_fupd ip E e Φ : WP e @ ip; E {{ v, |={E}=> Φ v }} ⊢ WP e @ ip; E {{ Φ }}.
Proof. iIntros "H". iApply (aneris_wp_strong_mono ip E with "H"); auto. Qed.

Lemma aneris_wp_atomic ip E1 E2 e Φ `{!Atomic WeaklyAtomic (mkExpr ip e)} :
  (|={E1,E2}=> WP e @ ip; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ ip; E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp Hin".
  iApply wp_atomic.
  iMod "Hwp"; iModIntro.
  iApply wp_mono; last by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> >Hw]"; eauto.
Qed.

Lemma aneris_wp_step_fupd ip E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ ip; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ ip; E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He HE) "HP Hwp Hin".
  iApply (wp_step_fupd with "[$HP]"); [|done|].
  { rewrite /= /aneris_to_val He //. }
  iApply wp_mono; last by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> Hw]".
  iIntros "HP"; iMod ("Hw" with "HP"); eauto.
Qed.

Lemma aneris_wp_bind K ip E e Φ :
  WP e @ ip; E {{ v, WP fill K (of_val v) @ ip; E {{ Φ }} }} ⊢
  WP fill K e @ ip; E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp #Hin".
  rewrite aneris_ground_fill.
  iApply wp_bind; simpl.
  iApply wp_wand_r; iSplitL; first by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> Hw]".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  rewrite -aneris_ground_fill /=.
  iApply "Hw"; done.
Qed.

Local Lemma wp_preserves_node E ip e Ψ :
  WP (mkExpr ip e) @ E {{ Ψ }} ⊢
  WP (mkExpr ip e) @ E {{ λ u, ∃ w, ⌜u = mkVal ip w⌝ ∗ Ψ u }}.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (E ip e Ψ).
  rewrite !wp_unfold /wp_pre /= /aneris_to_val /=.
  destruct (to_val e); simpl; first by iMod "Hwp"; eauto.
  iIntros (σ1 κ _ _) "Hsi".
  iMod ("Hwp" $! σ1 κ [] 0 with "Hsi") as "[% Hstp]".
  iModIntro.
  iSplit; first done.
  iIntros (e2 σ2 efs Hpstp).
  assert (∃ e2', e2 = mkExpr ip e2') as [e2' ->].
  { inversion Hpstp as [? e1' ? He1' ? Hhstp]; simplify_eq/=.
    destruct e1'.
    rewrite -aneris_ground_fill in He1'; simplify_eq/=.
    inversion Hhstp; simplify_eq; rewrite -aneris_ground_fill; eauto. }
  iMod ("Hstp" $! (mkExpr ip e2') σ2 efs with "[//]") as "Hstp".
  iModIntro; iNext.
  iMod "Hstp" as "(Hsi & Hwp & Hefs)".
  iModIntro; iFrame.
  iApply "IH"; done.
Qed.

Lemma aneris_wp_bind_inv K ip E e Φ :
  WP fill K e @ ip; E {{ Φ }} ⊢
  WP e @ ip; E {{ v, WP fill K (of_val v) @ ip; E {{ Φ }} }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp Hin".
  rewrite aneris_ground_fill.
  iApply wp_wand_r; iSplitL.
  { iApply wp_preserves_node.
    iApply (wp_bind_inv (fill (Λ := aneris_ectxi_lang) K)).
    iApply "Hwp"; done. }
  iIntros (v) "Hv"; simpl. iDestruct "Hv" as (w) "[-> Hw]".
  iExists w; iSplit; first done.
  rewrite -aneris_ground_fill /=.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hin"; done.
Qed.

(** * Derived rules *)
Lemma aneris_wp_mono ip E e Φ Ψ :
  (∀ v, Φ v ⊢ Ψ v) → WP e @ ip; E {{ Φ }} ⊢ WP e @ ip; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (aneris_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma aneris_wp_weaken ip E e Φ :
  WP e @ ip; E {{ Φ }} ⊢ WP e @ ip; E {{ Φ }}.
Proof. apply aneris_wp_mono; done. Qed.
Lemma aneris_wp_mask_mono ip E1 E2 e Φ :
  E1 ⊆ E2 → WP e @ ip; E1 {{ Φ }} ⊢ WP e @ ip; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (aneris_wp_strong_mono with "H"); auto. Qed.
Global Instance aneris_wp_mono' ip E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (aneris_wp ip E e).
Proof. by intros Φ Φ' ?; apply aneris_wp_mono. Qed.
Global Instance aneris_wp_flip_mono' ip E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (aneris_wp ip E e).
Proof. by intros Φ Φ' ?; apply aneris_wp_mono. Qed.

Lemma aneris_wp_value ip E Φ e v : IntoVal e v → Φ v ⊢ WP e @ ip; E {{ Φ }}.
Proof. intros <-. by apply aneris_wp_value'. Qed.
Lemma aneris_wp_value_fupd' ip E Φ v :
  (|={E}=> Φ v) ⊢ WP of_val v @ ip; E {{ Φ }}.
Proof. intros. by rewrite -aneris_wp_fupd -aneris_wp_value'. Qed.
Lemma aneris_wp_value_fupd ip E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ ip; E {{ Φ }}.
Proof. intros. rewrite -aneris_wp_fupd -aneris_wp_value //. Qed.
Lemma aneris_wp_value_inv ip E Φ e v :
  IntoVal e v → IsNode ip -∗ WP e @ ip; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. apply aneris_wp_value_inv'. Qed.

Lemma aneris_wp_frame_l ip E e Φ R :
  R ∗ WP e @ ip; E {{ Φ }} ⊢ WP e @ ip; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[? H]". iApply (aneris_wp_strong_mono with "H"); auto with iFrame.
Qed.
Lemma aneris_wp_frame_r ip E e Φ R :
  WP e @ ip; E {{ Φ }} ∗ R ⊢ WP e @ ip; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros "[H ?]". iApply (aneris_wp_strong_mono with "H"); auto with iFrame.
Qed.

Lemma aneris_wp_frame_step_l ip E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ ip; E2 {{ Φ }} ⊢ WP e @ ip; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (aneris_wp_step_fupd with "Hu"); try done.
  iApply (aneris_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma aneris_wp_frame_step_r ip E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ ip; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ ip; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply aneris_wp_frame_step_l.
Qed.
Lemma aneris_wp_frame_step_l' ip E e Φ R :
  TCEq (to_val e) None →
  ▷ R ∗ WP e @ ip; E {{ Φ }} ⊢ WP e @ ip; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[??]". iApply (aneris_wp_frame_step_l ip E E); try iFrame; eauto.
Qed.
Lemma aneris_wp_frame_step_r' ip E e Φ R :
  TCEq (to_val e) None →
  WP e @ ip; E {{ Φ }} ∗ ▷ R ⊢ WP e @ ip; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "[??]". iApply (aneris_wp_frame_step_r ip E E); try iFrame; eauto.
 Qed.

Lemma aneris_wp_wand ip E e Φ Ψ :
  WP e @ ip; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ ip; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (aneris_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma aneris_wp_wand_l ip E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ ip; E {{ Φ }} ⊢ WP e @ ip; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (aneris_wp_wand with "Hwp H"). Qed.
Lemma aneris_wp_wand_r ip E e Φ Ψ :
  WP e @ ip; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ ip; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (aneris_wp_wand with "Hwp H"). Qed.
Lemma aneris_wp_frame_wand_l ip E e Q Φ :
  Q ∗ WP e @ ip; E {{ v, Q -∗ Φ v }} -∗ WP e @ ip; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (aneris_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End aneris_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!distG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Global Instance frame_wp p ip E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ ip; E {{ Φ }}) (WP e @ ip; E {{ Ψ }}).
  Proof.
    rewrite /Frame=> HR. rewrite aneris_wp_frame_l. apply aneris_wp_mono, HR.
  Qed.

  Global Instance is_except_0_wp ip E e Φ : IsExcept0 (WP e @ ip; E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd_aneris_wp -except_0_fupd -fupd_intro; done.
  Qed.

  Global Instance elim_modal_bupd_wp p ip E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ ip; E {{ Φ }}) (WP e @ ip; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_aneris_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p ip E e P Φ :
    ElimModal True p false (|={E}=> P) P
              (WP e @ ip; E {{ Φ }}) (WP e @ ip; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_aneris_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p ip E1 E2 e P Φ :
    Atomic (WeaklyAtomic) (mkExpr ip e) →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ ip; E1 {{ Φ }}) (WP e @ ip; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r aneris_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp ip E e P Φ :
    AddModal (|={E}=> P) P (WP e @ ip; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_aneris_wp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e ip Φ :
    Atomic (WeaklyAtomic) (mkExpr ip e) →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ ip; E1 {{ Φ }})
            (λ x, WP e @ ip; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (aneris_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e ip Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (WP e @ ip; E {{ Φ }})
            (λ x, WP e @ ip; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply aneris_wp_fupd.
    iApply (aneris_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

Notation "'WP' e '@[' ip ] E {{ Φ } }" := (wp ip E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  '@[' ip  ]  E  {{  Φ  } }") : bi_scope.
Notation "'WP' e '@[' ip ] {{ Φ } }" := (wp ip ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  '@[' ip ]  {{  Φ  } }") : bi_scope.

Notation "'WP' e '@[' ip ] E {{ v , Q } }" := (wp ip E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  '@[' ip ]  E  {{  v ,  Q  } }") : bi_scope.
Notation "'WP' e '@[' ip ] {{ v , Q } }" := (wp ip ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  '@[' ip ]  {{  v ,  Q  } }") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e '@[' ip ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[ip] E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  '@[' ip ]  E  {{{  x .. y ,  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e '@[' ip ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[ip] {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  '@[' ip ]  {{{  x .. y ,   RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e '@[' ip ] E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[ip] E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  '@[' ip ]  E  {{{  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e '@[' ip ] {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[ip] {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  '@[' ip ]  {{{  RET  pat ;  Q } } }") : bi_scope.

Notation "'{{{' P } } } e '@[' ip ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[ip] E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  '@[' ip ]  E  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e '@[' ip ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[ip] {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  '@[' ip ]  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e '@[' ip ] E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[ip] E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  '@[' ip ]  E  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e '@[' ip ] {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[ip] {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  '@[' ip ]  {{{  RET  pat ;  Q } } }") : stdpp_scope.

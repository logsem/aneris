From iris.proofmode Require Import base tactics classes.
From trillium.program_logic Require Export weakestpre.
From aneris.aneris_lang Require Export resources network base_lang.
From aneris.aneris_lang.state_interp Require Import state_interp_def state_interp.
From aneris.aneris_lang Require Import lifting resources network base_lang.
From aneris.lib Require Import singletons.

Set Default Proof Using "Type".

Definition aneris_wp_def `{!anerisG Mdl Σ} (ip : ip_address) (E : coPset)
           (e : expr) (Φ : val → iProp Σ) : iProp Σ:=
  (∀ tid, is_node ip -∗
   wp NotStuck E (ip, tid) (mkExpr ip e) (λ v, ∃ w, ⌜v = mkVal ip w⌝ ∗ Φ w))%I.

Definition aneris_wp_aux `{!anerisG Mdl Σ} : seal (@aneris_wp_def Mdl Σ _).
Proof. by eexists. Qed.
Definition aneris_wp `{!anerisG Mdl Σ} := aneris_wp_aux.(unseal).
Definition aneris_wp_eq `{!anerisG Mdl Σ} : aneris_wp = @aneris_wp_def Mdl Σ _ :=
  aneris_wp_aux.(seal_eq).

Notation "'WP' e '@[' ip ] E {{ Φ } }" := (aneris_wp ip E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  '@[' ip  ]  E  {{  Φ  } }") : bi_scope.
Notation "'WP' e '@[' ip ] {{ Φ } }" := (aneris_wp ip ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  '@[' ip ]  {{  Φ  } }") : bi_scope.

Notation "'WP' e '@[' ip ] E {{ v , Q } }" := (aneris_wp ip E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  '@[' ip ]  E  {{  v ,  Q  } }") : bi_scope.
Notation "'WP' e '@[' ip ] {{ v , Q } }" := (aneris_wp ip ⊤ e%E (λ v, Q))
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

Section aneris_wp.
Context `{!anerisG Mdl Σ}.
Implicit Types ip : ip_address.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

(* This lifts a primitive wp into the aneris wp that hides the node *)
Lemma aneris_wp_lift tid ip e E Φ :
  is_node ip -∗ aneris_wp ip E e Φ -∗
  wp NotStuck E (ip,tid) (mkExpr ip e) (λ w, ∃ v, ⌜w = mkVal ip v⌝ ∗ Φ v).
Proof. iIntros "Hnode Hwp". rewrite aneris_wp_eq. by iApply "Hwp". Qed.

(* Weakest pre *)
Lemma aneris_wp_unfold ip E e Φ :
  WP e @[ip] E {{ Φ }} ⊣⊢ aneris_wp_def ip E e Φ.
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
  do 3 f_equiv.
  apply wp_contractive.
  - rewrite /= /aneris_to_val Htv //.
  - destruct k; first done.
    solve_proper.
Qed.

Lemma aneris_wp_value' ip E Φ v : Φ v ⊢ WP of_val v @[ip] E {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite aneris_wp_unfold /aneris_wp_def.
  iIntros (tid) "Hin".
  iApply wp_value; eauto.
 Qed.

Lemma aneris_wp_is_node ip E Φ e :
  (is_node ip -∗ WP e @[ip] E {{ Φ }}) ⊢ WP e @[ip] E {{ Φ }}.
Proof.
  rewrite aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp %tid #Hin".
  iApply "Hwp"; done.
 Qed.

Lemma aneris_wp_strong_mono ip E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  WP e @[ip] E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @[ip] E2 {{ Ψ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (HE) "Hwp HΦ %tid Hin".
  iSpecialize ("Hwp" $! tid).
  iApply (wp_strong_mono with "[Hin Hwp]"); [done|done|iApply "Hwp"; done|].
  iIntros (?); iDestruct 1 as (w) "[-> Hw]".
  iMod ("HΦ" with "Hw"); eauto.
Qed.

Lemma fupd_aneris_wp ip E e Φ :
  (|={E}=> WP e @[ip] E {{ Φ }}) ⊢ WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp %tid Hin".
  iApply fupd_wp; iMod "Hwp"; iModIntro.
  iApply "Hwp"; done.
Qed.

Lemma aneris_wp_fupd ip E e Φ :
  WP e @[ip] E {{ v, |={E}=> Φ v }} ⊢ WP e @[ip] E {{ Φ }}.
Proof. iIntros "H". iApply (aneris_wp_strong_mono ip E with "H"); auto. Qed.

Lemma aneris_wp_atomic ip E1 E2 e Φ `{!Atomic WeaklyAtomic (mkExpr ip e)} :
  (|={E1,E2}=> WP e @[ip] E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp %tid Hin".
  iApply wp_atomic. simpl.
  iMod "Hwp"; iModIntro.
  iApply wp_mono; last by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> >Hw]"; eauto.
Qed.

Lemma aneris_wp_atomic_take_step ip E1 E2 e Φ
      `{!Atomic WeaklyAtomic (mkExpr ip e)} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ (extr : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c1,
     ⌜trace_ends_in extr c1⌝ →
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ c2 δ2 ℓ oζ,
           ∃ δ' ℓ',
           state_interp
             (trace_extend extr oζ c2)
             (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗
           state_interp
             (trace_extend extr oζ c2)
             (trace_extend atr ℓ' δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @[ip] E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hwp %tid Hisnode".
  iApply (wp_atomic_take_step _ _ E2).
  { rewrite /= /aneris_to_val He //. }
  iMod "Hwp". iModIntro.
  iIntros (ex atr c1 δ1 ζ' Hδ1 Hatr <-) "Hsi".
  iDestruct ("Hwp" with "[] Hsi") as "> Hwp"; first done.
  iDestruct "Hwp" as (Q R) "(Hsi & H1 & H2 & Hwp)".
  iModIntro.
  iExists Q, R; iFrame.
  iSplitL "H1".
  { iIntros (c2 δ2 ℓ). iSpecialize ("H1" $! c2 δ2 ℓ (Some (ip, tid))).
    iFrame. }
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iDestruct ("Hwp" with "Hisnode") as "Hwp".
  iApply wp_wand_r; iFrame.
  iIntros (v) "H". iDestruct "H" as (w) "[-> HQimp]".
  iIntros "HR".
  iMod ("HQimp" with "HR").
  iModIntro; iExists _; iFrame; done.
Qed.

Lemma aneris_wp_stuttering_atomic ip E1 E2 e Φ
      `{!StutteringAtomic WeaklyAtomic (mkExpr ip e)} :
  (|={E1,E2}=> WP e @[ip] E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "He %tid Hn".
  iApply wp_stuttering_atomic.
  iMod "He". iModIntro.
  iApply wp_wand_r; iSplitL.
  { iApply ("He" with "Hn"). }
  iIntros (?). iDestruct 1 as (?) "[% HΦ]".
  iMod "HΦ". iModIntro. eauto.
Qed.

Lemma aneris_wp_stuttering_atomic_take_step ip E1 E2 e Φ
      `{!StutteringAtomic WeaklyAtomic (mkExpr ip e)} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ (extr : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c1,
     ⌜trace_ends_in extr c1⌝ →
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ c2 δ2 ℓ oζ,
           ∃ δ',
           state_interp
             (trace_extend extr oζ c2)
             (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗
           state_interp
             (trace_extend extr oζ c2)
             (trace_extend atr stuttering_label δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @[ip] E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hwp %tid Hisnode".
  iApply (wp_stutteringatomic_take_step _ _ E2).
  { rewrite /= /aneris_to_val He //. }
  iMod "Hwp". iModIntro.
  iIntros (ex atr c1 δ1 ? Hδ1 Hatr <-) "Hsi".
  iDestruct ("Hwp" with "[] Hsi") as "> Hwp"; first done.
  iDestruct "Hwp" as (Q R) "(Hsi & H1 & H2 & Hwp)".
  iModIntro.
  iExists _, _; iFrame.
  iSplitL "H1".
  { iIntros (c2 δ2 ℓ). iSpecialize ("H1" $! c2 δ2 ℓ (Some (ip, tid))).
    iFrame. }
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iDestruct ("Hwp" with "Hisnode") as "Hwp".
  iApply wp_wand_r; iFrame.
  iIntros (v) "H". iDestruct "H" as (w) "[-> HQimp]".
  iIntros "HR".
  iMod ("HQimp" with "HR").
  iModIntro; iExists _; iFrame; done.
Qed.

Lemma aneris_wp_lb_get ip E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @[ip] E {{ v, Φ v }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hwp".
  iIntros (tid) "Hip".
  rewrite !wp_unfold /wp_pre /= /aneris_to_val /= He.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe)
          "(?&?&?&?&Hauth)".
  iDestruct (steps_lb_get with "Hauth") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb'"; [lia|].
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iDestruct ("Hwp" with "Hlb' Hip") as "Hwp".
  rewrite !wp_unfold /wp_pre /= /aneris_to_val /= He.
  iMod ("Hwp" with "[//] [//] [//] [$]") as "[% H]".
  iModIntro.
  iSplit; [done|].
  iIntros (e2 σ2 efs Hstep). simpl.
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H". iMod "H" as (δ2 ℓ) "((?&?&?&?&Hauth) & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iExists δ2, ℓ.
  iFrame.
Qed.

Lemma aneris_wp_lb_update ip n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @[ip] E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hlb Hwp".
  iIntros (tid) "Hip".
  iDestruct ("Hwp" with "Hip") as "Hwp".
  rewrite !wp_unfold /wp_pre /=.
  rewrite /aneris_to_val. simpl. rewrite He. simpl.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe)
          "(?&?&?&?&Hauth)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iDestruct (steps_lb_valid with "Hauth Hlb") as %Hle.
  iMod ("Hwp" with "[//] [//] [//] [$]") as "[% H]".
  iModIntro.
  iSplit; [done|].
  iIntros (e2 σ2 efs Hstep). simpl.
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H". iMod "H" as (δ2 ℓ) "((?&?&?&?&Hauth) & H & Hefs)".
  iDestruct (steps_lb_get with "Hauth") as "#Hlb'".
  iDestruct (steps_lb_le _ (S n) with "Hlb'") as "#Hlb''"; [lia|].
  iMod "Hclose" as "_". iModIntro.
  iExists δ2, ℓ.
  iFrame.
  iApply (wp_wand with "H").
  iIntros (v) "H".
  iDestruct "H" as (w Heq) "H".
  iExists _. iSplit; [done|]. by iApply "H".
Qed.

Lemma aneris_wp_step_fupdN ip n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ extr atr, state_interp extr atr
       ={E1,∅}=∗ ⌜n ≤ S (trace_length extr)⌝%nat) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @[ip] E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He HE) "H %tid Hin".
  iApply (wp_step_fupdN with "[H Hin]"); [|done|].
  { rewrite /= /aneris_to_val He //. }
  iSplit; [by iDestruct "H" as "[H _]"|].
  iDestruct "H" as "[_ [$ Hwp]]".
  iApply wp_mono; last by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> Hw]".
  iIntros "HP"; iMod ("Hw" with "HP"); eauto.
Qed.

Lemma aneris_wp_lb_step ip n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WP e @[ip] E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @[ip] E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hwp".
  iApply aneris_wp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (extr atr) "(? & ? & ? & ? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. lia.
Qed.

Lemma aneris_wp_step_fupd ip E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @[ip] E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @[ip] E1 {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He HE) "HP Hwp %tid Hin".
  iApply (wp_step_fupd with "[$HP]"); [|done|].
  { rewrite /= /aneris_to_val He //. }
  iApply wp_mono; last by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> Hw]".
  iIntros "HP"; iMod ("Hw" with "HP"); eauto.
Qed.

Lemma aneris_wp_socket_interp_alloc_group_singleton Ψ ip E e Φ sag :
  TCEq (to_val e) None →
  unfixed_groups {[sag]} -∗
  (sag ⤇* Ψ -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hsag Hwp %tid Hin".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val.
  rewrite He. simpl.
  iIntros (extr atr K tp1 tp2 σ1 Hextr Hlocale Htr).
  iIntros "(Hev & Hσ & H)".
  iMod (aneris_state_interp_socket_interp_allocate_singleton with "Hσ Hsag")
    as "[Hσ HΨ]".
  iDestruct ("Hwp" with "HΨ Hin") as "Hwp".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val He.
  iApply ("Hwp" with "[//] [//] [//] [$Hev $Hσ $H]").
Qed.

Lemma aneris_wp_socket_interp_alloc_group_fun f ip E e Φ sags :
  TCEq (to_val e) None →
  unfixed_groups sags -∗
  (([∗ set] sag ∈ sags, sag ⤇* f sag) -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hsag Hwp %tid Hin".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val.
  rewrite He. simpl.
  iIntros (extr atr K tp1 tp2 σ1 Hextr Hlocale Htr).
  iIntros "(Hev & Hσ & H)".
  iMod (aneris_state_interp_socket_interp_allocate_fun with "Hσ Hsag") as "[Hσ HΨ]".
  iDestruct ("Hwp" with "HΨ Hin") as "Hwp".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val He.
  iApply ("Hwp" with "[//] [//] [//] [$Hev $Hσ $H]").
Qed.

Lemma aneris_wp_socket_interp_alloc_group Ψ ip E e Φ sags :
  TCEq (to_val e) None →
  unfixed_groups sags -∗
  (([∗ set] sag ∈ sags, sag ⤇* Ψ) -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros (He) "Hsag Hwp %tid Hin".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val.
  rewrite He. simpl.
  iIntros (extr atr K tp1 tp2 σ1 Hextr Hlocale Htr).
  iIntros "(Hev & Hσ & H)".
  iMod (aneris_state_interp_socket_interp_allocate with "Hσ Hsag") as "[Hσ HΨ]".
  iDestruct ("Hwp" with "HΨ Hin") as "Hwp".
  rewrite !wp_unfold /wp_def /wp_pre. simpl. rewrite /aneris_to_val He.
  iApply ("Hwp" with "[//] [//] [//] [$Hev $Hσ $H]").
Qed.

Lemma aneris_wp_socket_interp_alloc_singleton Ψ ip E e Φ sa :
  TCEq (to_val e) None →
  unfixed {[sa]} -∗
  (sa ⤇ Ψ -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  iIntros (He) "Hsag Hwp".
  iApply (aneris_wp_socket_interp_alloc_group_singleton _ _ _ _ _ {[sa]}
           with "[Hsag]");
    [|done].
  by rewrite /unfixed /to_singletons gset_map.gset_map_singleton.
Qed.

Lemma aneris_wp_socket_interp_alloc_fun f ip E e Φ sas :
  TCEq (to_val e) None →
  unfixed sas -∗
  (([∗ set] sa ∈ sas, sa ⤇ f sa) -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  iIntros (He) "Hsag Hwp".
  iApply (aneris_wp_socket_interp_alloc_group_fun (λ x, from_singleton $ f (hd inhabitant (elements x))) _ _ _ _ (to_singletons sas)
           with "Hsag").
  iIntros "Hsags". iApply ("Hwp" with "[Hsags]").
  iInduction sas as [|sag sags Hnin] "IHsags" using set_ind_L; [done|].
  rewrite to_singletons_union. rewrite big_sepS_union; [|set_solver].
  rewrite big_sepS_union; [| by rewrite to_singletons_inv; set_solver].
  iDestruct "Hsags" as "[Hsag Hsags]".
  iDestruct ("IHsags" with "Hsags") as "H".
  rewrite to_singletons_inv !big_sepS_singleton (elements_singleton _).
  by iFrame.
Qed.

Lemma aneris_wp_socket_interp_alloc Ψ ip E e Φ sas :
  TCEq (to_val e) None →
  unfixed sas -∗
  (([∗ set] sa ∈ sas, sa ⤇ Ψ) -∗ WP e @[ip] E {{ Φ }}) -∗
  WP e @[ip] E {{ Φ }}.
Proof.
  iIntros (He) "Hsag Hwp".
  iApply (aneris_wp_socket_interp_alloc_group _ _ _ _ _ (to_singletons sas)
           with "Hsag").
  iIntros "Hsags". iApply ("Hwp" with "[Hsags]").
  iInduction sas as [|sag sags Hnin] "IHsags" using set_ind_L; [done|].
  rewrite to_singletons_union. rewrite big_sepS_union; [|set_solver].
  rewrite big_sepS_union; [| by rewrite to_singletons_inv; set_solver].
  iDestruct "Hsags" as "[Hsag Hsags]".
  iDestruct ("IHsags" with "Hsags") as "$".
  by rewrite to_singletons_inv !big_sepS_singleton.
Qed.

Lemma aneris_wp_bind K ip E e Φ :
  WP e @[ip] E {{ v, WP fill K (of_val v) @[ip] E {{ Φ }} }} ⊢
  WP fill K e @[ip] E {{ Φ }}.
Proof.
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iIntros "Hwp %tid #Hin".
  rewrite aneris_base_fill.
  iApply wp_bind; simpl.
  iApply wp_wand_r; iSplitL; first by iApply "Hwp".
  iIntros (v); iDestruct 1 as (w) "[-> Hw]".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  rewrite -aneris_base_fill /=.
  iApply "Hw"; done.
Qed.

Local Lemma wp_preserves_node E ip e Ψ ζ:
  WP (mkExpr ip e) @ ζ; E {{ Ψ }} ⊢
  WP (mkExpr ip e) @ ζ; E {{ λ u, ∃ w, ⌜u = mkVal ip w⌝ ∗ Ψ u }}.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (E ip e Ψ).
  rewrite !wp_unfold /wp_pre /= /aneris_to_val /=.
  destruct (to_val e); simpl; first by iMod "Hwp"; eauto.
  iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "Hsi".
  iMod ("Hwp" with "[//] [//] [//] Hsi") as "[% Hstp]".
  iModIntro.
  iSplit; first done.
  iIntros (e2 σ2 efs Hpstp).
  assert (∃ e2', e2 = mkExpr ip e2') as [e2' ->].
  { inversion Hpstp as [? e1' ? He1' ? Hhstp]; simplify_eq/=.
    destruct e1'.
    rewrite -aneris_base_fill in He1'; simplify_eq/=.
    inversion Hhstp; simplify_eq; rewrite -aneris_base_fill; eauto. }
  iMod ("Hstp" $! (mkExpr ip e2') σ2 efs with "[//]") as "Hstp".
  iModIntro; iNext.
  assert (∃ n, n = trace_length ex) as [n Heqn] by eauto.
  rewrite -{1}Heqn. rewrite -{2}Heqn. clear Heqn.
  assert (∃ n', n' = trace_length ex) as [n' Heqn'] by eauto.
  rewrite -Heqn'. clear Heqn'.
  iInduction (n) as [|n] "IHlen" forall (n'); last first.
  { iMod ("IHlen" with "Hstp") as "H". done. }
  iMod "Hstp". iModIntro.
  iMod "Hstp" as (δ' ℓ) "(Hsi & Hwp & Hefs)".
  iModIntro; iFrame.
  iExists _, ().  iFrame.
  iApply "IH"; done.
Qed.

(** * Derived rules *)
Lemma aneris_wp_mono ip E e Φ Ψ :
  (∀ v, Φ v ⊢ Ψ v) → WP e @[ip] E {{ Φ }} ⊢ WP e @[ip] E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (aneris_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma aneris_wp_weaken ip E e Φ :
  WP e @[ip] E {{ Φ }} ⊢ WP e @[ip] E {{ Φ }}.
Proof. apply aneris_wp_mono; done. Qed.
Lemma aneris_wp_mask_mono ip E1 E2 e Φ :
  E1 ⊆ E2 → WP e @[ip] E1 {{ Φ }} ⊢ WP e @[ip] E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (aneris_wp_strong_mono with "H"); auto. Qed.
Global Instance aneris_wp_mono' ip E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (aneris_wp ip E e).
Proof. by intros Φ Φ' ?; apply aneris_wp_mono. Qed.
Global Instance aneris_wp_flip_mono' ip E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (aneris_wp ip E e).
Proof. by intros Φ Φ' ?; apply aneris_wp_mono. Qed.

Lemma aneris_wp_value ip E Φ e v : IntoVal e v → Φ v ⊢ WP e @[ip] E {{ Φ }}.
Proof. intros <-. by apply aneris_wp_value'. Qed.
Lemma aneris_wp_value_fupd ip E Φ v :
  (|={E}=> Φ v) ⊢ WP of_val v @[ip] E {{ Φ }}.
Proof. intros. by rewrite -aneris_wp_fupd -aneris_wp_value'. Qed.
Lemma aneris_wp_value_fupd' ip E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @[ip] E {{ Φ }}.
Proof. intros. rewrite -aneris_wp_fupd -aneris_wp_value //. Qed.

Lemma aneris_wp_frame_l ip E e Φ R :
  R ∗ WP e @[ip] E {{ Φ }} ⊢ WP e @[ip] E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[? H]". iApply (aneris_wp_strong_mono with "H"); auto with iFrame.
Qed.
Lemma aneris_wp_frame_r ip E e Φ R :
  WP e @[ip] E {{ Φ }} ∗ R ⊢ WP e @[ip] E {{ v, Φ v ∗ R }}.
Proof.
  iIntros "[H ?]". iApply (aneris_wp_strong_mono with "H"); auto with iFrame.
Qed.

Lemma aneris_wp_frame_step_l ip E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @[ip] E2 {{ Φ }} ⊢ WP e @[ip] E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (aneris_wp_step_fupd with "Hu"); try done.
  iApply (aneris_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma aneris_wp_frame_step_r ip E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @[ip] E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @[ip] E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @[_] _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply aneris_wp_frame_step_l.
Qed.
Lemma aneris_wp_frame_step_l' ip E e Φ R :
  TCEq (to_val e) None →
  ▷ R ∗ WP e @[ip] E {{ Φ }} ⊢ WP e @[ip] E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[??]". iApply (aneris_wp_frame_step_l ip E E); try iFrame; eauto.
Qed.
Lemma aneris_wp_frame_step_r' ip E e Φ R :
  TCEq (to_val e) None →
  WP e @[ip] E {{ Φ }} ∗ ▷ R ⊢ WP e @[ip] E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "[??]". iApply (aneris_wp_frame_step_r ip E E); try iFrame; eauto.
 Qed.

Lemma aneris_wp_wand ip E e Φ Ψ :
  WP e @[ip] E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @[ip] E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (aneris_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma aneris_wp_wand_l ip E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @[ip] E {{ Φ }} ⊢ WP e @[ip] E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (aneris_wp_wand with "Hwp H"). Qed.
Lemma aneris_wp_wand_r ip E e Φ Ψ :
  WP e @[ip] E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @[ip] E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (aneris_wp_wand with "Hwp H"). Qed.
Lemma aneris_wp_frame_wand_l ip E e Q Φ :
  Q ∗ WP e @[ip] E {{ v, Q -∗ Φ v }} -∗ WP e @[ip] E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (aneris_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End aneris_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!anerisG Mdl Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Global Instance frame_wp p ip E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @[ip] E {{ Φ }}) (WP e @[ip] E {{ Ψ }}).
  Proof.
    rewrite /Frame=> HR. rewrite aneris_wp_frame_l. apply aneris_wp_mono, HR.
  Qed.

  Global Instance is_except_0_wp ip E e Φ : IsExcept0 (WP e @[ip] E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd_aneris_wp -except_0_fupd -fupd_intro; done.
  Qed.

  Global Instance elim_modal_bupd_wp p ip E e P Φ :
    ElimModal True p false (|==> P) P (WP e @[ip] E {{ Φ }}) (WP e @[ip] E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_aneris_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p ip E e P Φ :
    ElimModal True p false (|={E}=> P) P
              (WP e @[ip] E {{ Φ }}) (WP e @[ip] E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_aneris_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_stutteringatomic p ip E1 E2 e P Φ :
    StutteringAtomic WeaklyAtomic (mkExpr ip e) →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @[ip] E1 {{ Φ }}) (WP e @[ip] E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r aneris_wp_stuttering_atomic.
  Qed.

  Global Instance add_modal_fupd_wp ip E e P Φ :
    AddModal (|={E}=> P) P (WP e @[ip] E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_aneris_wp. Qed.

  Global Instance elim_acc_wp_stuttering {X} E1 E2 α β γ e ip Φ :
    StutteringAtomic WeaklyAtomic (mkExpr ip e) →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @[ip] E1 {{ Φ }})
            (λ x, WP e @[ip] E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (aneris_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e ip Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @[ip] E {{ Φ }})
            (λ x, WP e @[ip] E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply aneris_wp_fupd.
    iApply (aneris_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

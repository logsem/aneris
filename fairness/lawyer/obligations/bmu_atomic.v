From stdpp Require Import coPset namespaces.
From iris.bi Require Export bi updates.
From iris.bi.lib Require Import fixpoint.
From iris.proofmode Require Import coq_tactics proofmode reduction.
From iris.prelude Require Import options.
From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.


(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  Context
    (* {PROP : bi} `{!BiFUpd PROP} *)
    {TA TB : tele}.

  Notation "'PROP'" := (iProp Σ). 
  
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  Context (c: nat).
  Let bmu E := BMU E c (oGS := oGS).

  (** atomic_acc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  Definition BMU_atomic_acc Eo Ei α P β Φ: PROP :=
    |={Eo, Ei}=> ∃.. x, α x ∗
          ((α x ={Ei, Eo}=∗ P) ∧ (∀.. y, β x y -∗ bmu Ei (|={Ei, Eo}=> Φ x y))).

  Lemma BMU_atomic_acc_wand Eo Ei α P1 P2 β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀.. x y, Φ1 x y -∗ Φ2 x y)) -∗
    (BMU_atomic_acc Eo Ei α P1 β Φ1 -∗ BMU_atomic_acc Eo Ei α P2 β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iSpecialize ("Hclose" with "[$]"). iApply (BMU_wand with "[-Hclose] [$]").
      iIntros "X". iMod "X". iModIntro. 
      by iApply "HP12". 
  Qed.

  (* Lemma BMU_atomic_acc_mask Eo Ed α P β Φ : *)
  (*   BMU_atomic_acc Eo (Eo∖Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → BMU_atomic_acc E (E∖Ed) α P β Φ. *)
  (* Proof. *)
  (*   iSplit; last first. *)
  (*   { iIntros "Hstep". iApply ("Hstep" with "[% //]"). } *)
  (*   iIntros "Hstep" (E HE). *)
  (*   iApply (fupd_mask_frame_acc with "Hstep"); first done. *)
  (*   iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]". *)
  (*   iIntros "!> Hclose'". *)
  (*   iExists x. iFrame. iSplitWith "Hclose". *)
  (*   - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done. *)
  (*   - iIntros (y) "Hβ". *)
  (*     iSpecialize ("Hclose" with "[$]"). iApply (BMU_wand with "[-Hclose] [$]"). *)
  (*     iApply "Hclose'". iApply "Hclose". done. *)
  (* Qed. *)

  Lemma BMU_atomic_acc_mask_weaken Eo1 Eo2 Ei α P β Φ :
    Eo1 ⊆ Eo2 →
    BMU_atomic_acc Eo1 Ei α P β Φ -∗ BMU_atomic_acc Eo2 Ei α P β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod (fupd_mask_subseteq Eo1) as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iSplitWith "Hclose2".
    - iIntros "Hα". iMod ("Hclose2" with "Hα") as "$". done.
    - iIntros (y) "Hβ".
      iSpecialize ("Hclose2" with "[$]"). iApply (BMU_wand with "[-Hclose2] [$]").
      iIntros "X". iMod "X". iMod "Hclose1". done. 
  Qed.

  (** atomic_update as a fixed-point of the equation
   AU = atomic_acc α AU β Q
  *)
  Context Eo Ei α β Φ.

  Definition BMU_atomic_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    BMU_atomic_acc Eo Ei α (Ψ ()) β Φ.

  Local Instance BMU_atomic_update_pre_mono : BiMonoPred BMU_atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
      iApply (BMU_atomic_acc_wand with "[HP12] AU").
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Local Definition BMU_atomic_update_def :=
    bi_greatest_fixpoint BMU_atomic_update_pre ().

End definition.

(** Seal it *)
Local Definition BMU_atomic_update_aux : seal (@BMU_atomic_update_def).
Proof. by eexists. Qed.
Definition BMU_atomic_update := BMU_atomic_update_aux.(unseal).
Global Arguments BMU_atomic_update {Σ _ _ _ _ _ _ TA TB}.
Local Definition BMU_atomic_update_unseal :
  @BMU_atomic_update = _ := BMU_atomic_update_aux.(seal_eq).

Global Arguments BMU_atomic_acc {Σ _ _ _ _ _ _ TA TB} c Eo Ei _ _ _ _ : simpl never.
Global Arguments BMU_atomic_update {Σ _ _ _ _ _ _ TA TB} c Eo Ei _ _ _ : simpl never.

(** Notation: Atomic updates *)
(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'BAU' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (BMU_atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv   ' 'BAU'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAU' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (BMU_atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
                 (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[hv   ' 'BAU'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAU' '<{' α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (BMU_atomic_update (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app α%I)
                 (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
                 (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv   ' 'BAU'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAU' '<{' α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (BMU_atomic_update (TA:=TeleO) (TB:=TeleO)
                 Eo Ei
                 (tele_app α%I)
                 (tele_app $ tele_app β%I)
                 (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[hv   ' 'BAU'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'BAACC' '<{' ∃∃ x1 .. xn , α , 'ABORT' P '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (BMU_atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, β%I) .. )
                     ) .. )
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, Φ%I) .. )
                     ) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv     ' 'BAACC'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAACC' '<{' ∃∃ x1 .. xn , α , 'ABORT' P '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (BMU_atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
              (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder,
   format "'[hv     ' 'BAACC'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAACC' '<{' α , 'ABORT' P '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (BMU_atomic_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
              (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv     ' 'BAACC'  '<{'  '[' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'BAACC' '<{' α , 'ABORT' P '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (BMU_atomic_acc (TA:=TeleO)
              (TB:=TeleO)
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app $ tele_app β%I)
              (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200,
   format "'[hv     ' 'BAACC'  '<{'  '[' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  (* Context `{BiFUpd PROP} {TA TB : tele}. *)
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  Context
    (* {PROP : bi} `{!BiFUpd PROP} *)
    {TA TB : tele}.
  Implicit Types (α : TA → iProp Σ) (β Φ : TA → TB → iProp Σ).

  Local Existing Instance BMU_atomic_update_pre_mono.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance BMU_ne c Ei n:
    Proper (
        dist n ==> dist n
    ) (BMU Ei c (oGS := oGS)).
  Proof. solve_proper. Qed.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance BMU_atomic_acc_ne c Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        dist n ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (BMU_atomic_acc c Eo Ei (oGS := oGS)).
  Proof. solve_proper. Qed. 

  Global Instance BMU_atomic_update_ne c Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (BMU_atomic_update c Eo Ei (oGS := oGS)).
  Proof.
    rewrite BMU_atomic_update_unseal /BMU_atomic_update_def /BMU_atomic_update_pre. solve_proper.
  Qed.

  Lemma BMU_atomic_update_mask_weaken c Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    BMU_atomic_update c Eo1 Ei α β Φ (oGS := oGS) -∗ BMU_atomic_update c Eo2 Ei α β Φ (oGS := oGS).
  Proof.
    rewrite BMU_atomic_update_unseal {2}/BMU_atomic_update_def /=.
    iIntros (Heo) "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, BMU_atomic_update_def c Eo1 Ei α β Φ)); last done.
    iIntros "!> *". rewrite {1}/BMU_atomic_update_def /= greatest_fixpoint_unfold.
    iApply BMU_atomic_acc_mask_weaken. done.
    Unshelve. apply _. 
  Qed.

  Local Lemma aupd_unfold c Eo Ei α β Φ :
    BMU_atomic_update c Eo Ei α β Φ (oGS := oGS) ⊣⊢
    BMU_atomic_acc c Eo Ei α (BMU_atomic_update c Eo Ei α β Φ (oGS := oGS)) β Φ (oGS := oGS).
  Proof.
    rewrite BMU_atomic_update_unseal /BMU_atomic_update_def /=. apply: greatest_fixpoint_unfold.
  Qed.

  (** The elimination form: an atomic accessor *)
  Lemma BMU_aupd_aacc c Eo Ei α β Φ :
    BMU_atomic_update c Eo Ei α β Φ (oGS := oGS) ⊢
    BMU_atomic_acc c Eo Ei α (BMU_atomic_update c Eo Ei α β Φ (oGS := oGS)) β Φ (oGS := oGS).
  Proof using Type*. by rewrite {1}aupd_unfold. Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_mod_aupd φ c Eo Ei E α β Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (BMU_atomic_update c Eo Ei α β Φ (oGS := oGS))
              (∃.. x, α x ∗
                       (α x ={Ei,E}=∗ BMU_atomic_update c Eo Ei α β Φ (oGS := oGS)) ∧
                       (* (∀.. y, β x y ={Ei,E}=∗ Φ x y) *)
                        (∀.. y, β x y -∗ BMU Ei c (|={Ei, E}=> Φ x y) (oGS := oGS))
              )
              Q Q'.
  Proof using H1 H0 H. 
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (BMU_aupd_aacc with "AU") as "AC".
    iMod (BMU_atomic_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  (** The introduction lemma for atomic_update. This should usually not be used
  directly; use the [iAuIntro] tactic instead. *)
  Local Lemma BMU_aupd_intro c P Q α β Eo Ei Φ :
    Absorbing P → Persistent P →
    (P ∧ Q ⊢ BMU_atomic_acc c Eo Ei α Q β Φ (oGS := oGS)) →
    P ∧ Q ⊢ BMU_atomic_update c Eo Ei α β Φ (oGS := oGS).
  Proof.
    rewrite BMU_atomic_update_unseal {1}/BMU_atomic_update_def /=.
    iIntros (?? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coiter _ (λ _, Q)); last done. iIntros "!>" ([]) "HQ".
    iApply HAU. iSplit; by iFrame.
  Qed.

  Lemma BMU_aacc_intro c Eo Ei α P β Φ :
    Ei ⊆ Eo → ⊢ (∀.. x, α x -∗
    ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y -∗ BMU Ei c (|={Ei, Eo}=> Φ x y) (oGS := oGS))) -∗
    BMU_atomic_acc c Eo Ei α P β Φ (oGS := oGS)).
  Proof.
    iIntros (? x) "Hα Hclose".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ".
      iApply (BMU_wand with "[Hclose']").
      2: { by iApply "Hclose". }
      iIntros "X". by iMod "X". 
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic accessor. *)
  Global Instance BMU_elim_acc_aacc {X} c E1 E2 Ei (α' β' : X → iProp Σ) γ' α β Pas Φ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (BMU_atomic_acc c E1 Ei α Pas β Φ (oGS := oGS))
            (λ x', BMU_atomic_acc c E2 Ei α (β' x' ∗ (γ' x' -∗? Pas))%I β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y)) (oGS := oGS)
            )%I.
  Proof.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose''".
    iExists x. iFrame. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros (y) "Hβ". iMod "Hclose''" as "_".
      (* iMod ("Hclose'" with "Hβ") as "Hβ'". *)
      iApply (BMU_wand with "[Hclose]").
      2: { by iApply "Hclose'". }
      iIntros "X". iMod "X" as "Hβ'". 
      (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  accessors can eliminate as well.  This is a forwarding instance needed because
  atomic_acc is becoming opaque. *)
  Global Instance BMU_elim_modal_acc p q φ c P P' Eo Ei α Pas β Φ :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (BMU_atomic_acc c Eo Ei α Pas β Φ (oGS := oGS))
              (BMU_atomic_acc c Eo Ei α Pas β Φ (oGS := oGS)).
  Proof. intros Helim. apply Helim. Qed.

    Ltac remember_goal :=
      match goal with | |- envs_entails _ ?P =>
        iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
      end.

  (** Lemmas for directly proving one atomic accessor in terms of another (or an *)
  (*     atomic update).  These are only really useful when the atomic accessor you *)
  (*     are trying to prove exactly corresponds to an atomic update/accessor you *)
  (*     have as an assumption -- which is not very common. *)
  Lemma BMU_aacc_aacc {TA' TB' : tele} E1 E1' E2 E3 c1 c2
        α P β Φ
        (α' : TA' → iProp Σ) P' (β' Φ' : TA' → TB' → iProp Σ) :
    E1' ⊆ E1 →
    E3 ⊆ E1 -> (* ! new condition for BMU *)
    BMU_atomic_acc c2 E1' E2 α P β Φ (oGS := oGS) -∗
    (∀.. x, α x -∗ BMU_atomic_acc c1 E2 E3 α' (α x ∗ (P ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (P ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')) (oGS := oGS)) -∗
    BMU_atomic_acc (c1 + c2) E1 E3 α' P' β' Φ' (oGS := oGS).
  Proof.
    iIntros (??) "Hupd Hstep".
    iMod (BMU_atomic_acc_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplit.
    - iIntros "Hα'". iDestruct "Hclose'" as "[Hclose' _]".
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". auto.
    - iIntros (y') "Hβ'". iDestruct "Hclose'" as "[_ Hclose']".
      iApply BMU_split. 
      (* iMod ("Hclose'" with "Hβ'") as "Hres". *)
      iApply (BMU_wand with "[Hclose]").
      2: { by iApply "Hclose'". }
      iIntros "X".
      iMod "X" as "Hres". 

      (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hres" as "[[Hα HΦ']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP".
        iIntros (??????) "X". iMod ("HΦ'" with "[$]"). iFrame.
        iExists x4. iFrame. eauto with iFrame.
        iApply fupd_frame_l. iSplit.
        { iPureIntro. lia. }
        iApply fupd_mask_subseteq. done. 
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct "Hcont" as (y) "[Hβ HΦ']".

        iSpecialize ("Hclose" with "[$]"). 
        iIntros (??????) "X". iMod ("Hclose" with "X") as "X".
        iDestruct "X" as (k) "(TI & %BOUND & Φ)".
        iExists k. iFrame. 
        iApply fupd_frame_l. iSplit.
        { iPureIntro. lia. }
        iMod "Φ". iMod ("HΦ'" with "Φ"). iFrame.  
        iApply fupd_mask_subseteq. done. 
  Qed.

  Notation "'PROP'" := (iProp Σ). 

  Lemma BMU_aacc_aupd {TA' TB' : tele} E1 E1' E2 E3 c1 c2
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    E3 ⊆ E1 ->
    BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) -∗
    (∀.. x, α x -∗ BMU_atomic_acc c1 E2 E3 α' (α x ∗ (BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')) (oGS := oGS)) -∗
    BMU_atomic_acc (c1 + c2) E1 E3 α' P' β' Φ' (oGS := oGS).
  Proof using H H0 H1.
    iIntros (??) "Hupd Hstep".
    iApply (BMU_aacc_aacc with "[Hupd] Hstep"). 
    3: { iApply BMU_aupd_aacc; done. }
    all: done.
  Qed.

  Lemma BMU_aacc_aupd_commit {TA' TB' : tele} E1 E1' E2 E3 c1 c2
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    E3 ⊆ E1 ->
    BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) -∗
    (∀.. x, α x -∗ BMU_atomic_acc c1 E2 E3 α' (α x ∗ (BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) ={E1}=∗ P')) β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')) (oGS := oGS)) -∗
    BMU_atomic_acc (c1 + c2) E1 E3 α' P' β' Φ' (oGS := oGS).
  Proof using H1 H0 H.
    iIntros (??) "Hupd Hstep". iApply (BMU_aacc_aupd with "Hupd").
    1, 2: done. 
    iIntros (x) "Hα". iApply BMU_atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iRight.
  Qed.

  Lemma BMU_aacc_aupd_abort {TA' TB' : tele} E1 E1' E2 E3 c1 c2
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    E3 ⊆ E1 ->
    BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) -∗
    (∀.. x, α x -∗ BMU_atomic_acc c1 E2 E3 α' (α x ∗ (BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) ={E1}=∗ P')) β'
            (λ.. x' y', α x ∗ (BMU_atomic_update c2 E1' E2 α β Φ (oGS := oGS) ={E1}=∗ Φ' x' y')) (oGS := oGS)) -∗
    BMU_atomic_acc (c1 + c2) E1 E3 α' P' β' Φ' (oGS := oGS).
  Proof using H1 H0 H.
    iIntros (??) "Hupd Hstep". iApply (BMU_aacc_aupd with "Hupd").
    1, 2: done. 
    iIntros (x) "Hα". iApply BMU_atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iLeft.
  Qed.

End lemmas.

(** ProofMode support for atomic updates. *)
Section proof_mode.
  (* Context `{BiFUpd PROP} {TA TB : tele}. *)
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  Context
    (* {PROP : bi} `{!BiFUpd PROP} *)
    {TA TB : tele}.
  Notation "'PROP'" := (iProp Σ). 
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Lemma tac_BMU_aupd_intro Γp Γs n α β Eo Ei Φ P c :
    P = env_to_prop Γs →
    envs_entails (Envs Γp Γs n) (BMU_atomic_acc c Eo Ei α P β Φ (oGS := oGS)) →
    envs_entails (Envs Γp Γs n) (BMU_atomic_update c Eo Ei α β Φ (oGS := oGS)).
  Proof.
    intros ->. rewrite envs_entails_unseal of_envs_eq /BMU_atomic_acc /=.
    setoid_rewrite env_to_prop_sound =>HAU.
    rewrite assoc. apply: BMU_aupd_intro. by rewrite -assoc.
  Qed.
End proof_mode.

(** * Now the coq-level tactics *)

Tactic Notation "BMUiAuIntro" :=
  match goal with
  | |- envs_entails (Envs ?Γp ?Γs _) (BMU_atomic_update _ _ _ _ _ ?Φ) =>
      notypeclasses refine (tac_BMU_aupd_intro Γp Γs _ _ _ _ _ Φ _ _ _ _); [
        (* P = ...: make the P pretty *) pm_reflexivity
      | (* the new proof mode goal *) ]
  end.

(** Tactic to apply [aacc_intro]. This only really works well when you have
[α ?] already and pass it as [iAaccIntro with "Hα"]. Doing
[rewrite /atomic_acc /=] is an entirely legitimate alternative. *)
Tactic Notation "BMUiAaccIntro" "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |-
    (* envs_entails _ (@atomic_acc ?PROP ?H ?TA ?TB ?Eo ?Ei ?α ?P ?β ?Φ) => *)
    envs_entails _ (@BMU_atomic_acc ?Σ ?H ?DegO ?LevelO ?LIM_STEPS
                      ?OPRE ?oGS ?TA ?TB ?c ?Eo ?Ei ?α ?P ?β ?Φ) =>
    iApply (@BMU_aacc_intro ?Σ ?H ?DegO ?LevelO ?LIM_STEPS
                      ?OPRE ?oGS ?TA ?TB ?c ?Eo ?Ei ?α ?P ?β ?Φ with sel);
    first try solve_ndisj; last iSplit
  | _ => fail "BMUiAAccIntro: Goal is not an atomic accessor"
  end.

(* From here on, prevent TC search from implicitly unfolding these. *)
Global Typeclasses Opaque BMU_atomic_acc BMU_atomic_update.

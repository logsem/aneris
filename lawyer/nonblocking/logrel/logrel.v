From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From lawyer.nonblocking.logrel Require Export persistent_pred substitutions.
From lawyer.nonblocking Require Export pwp. 
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
Import uPred.
From heap_lang Require Import heap_lang_defs.

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ: gFunctors}
    (* {iG: irisG heap_lang LoopingModel Σ} *)
    {invG: invGS_gen HasNoLc Σ}
    {hG: heap1GS Σ}. 
  Notation D := (persistent_predO (val heap_lang) (iPropI Σ)).
  Implicit Types ii : D.

  Local Arguments ofe_car !_.

  Program Definition interp_prod : D -n> D :=
    λne ii, PersPred (λ w, ▷ ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ ii w1 ∧ ii w2)%I.
  Next Obligation.
    solve_proper.
  Qed.
  Instance interp_prod_contractive : Contractive interp_prod.
  Proof. solve_contractive. Qed.

  Program Definition interp_sum : D -n> D :=
    λne ii,
      PersPred (λ w, ▷ ((∃ w1, ⌜w = InjLV w1⌝ ∧ ii w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ ii w2)))%I.
  Solve Obligations with solve_proper.
  Instance interp_sum_contractive : Contractive interp_sum.
  Proof. solve_contractive. Qed.

  Program Definition interp_arrow : D -n> D :=
    λne ii, PersPred (λ w, □ ∀ τ v, ▷ ii v →
      let _ := irisG_looping HeapLangEM si_add_none (lG := hG) in 
      pwp MaybeStuck CanFork ⊤ τ (App (of_val w) (of_val v)) ii )%I.
  Solve Obligations with solve_proper.
  Instance interp_arrow_contractive : Contractive interp_arrow.
  Proof.
    intros n interp interp' Hinterps w.
    rewrite /interp_arrow /=.
    f_equiv.
    f_equiv; intros v.
    f_equiv.
    red. intros a. f_equiv; [solve_contractive| ].  
    apply wp_contractive; first apply _.
    destruct n.
    { simpl in *. constructor. lia. }
    simpl. constructor. intros. by apply Hinterps.
  Qed.

  Program Definition interp_ref_inv (l : loc) : D -n> iPropO Σ :=
    λne ii, ((∃ v, l ↦ (v: val heap_lang) ∗ ii v) ∨ loc_freed l)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref : D -n> D :=
    λne ii, PersPred (λ w, ∃ l, ⌜w = LitV $ LitLoc l⌝ ∧ inv (logN .@ l) (interp_ref_inv l ii))%I.
  Solve Obligations with solve_proper.
  Instance interp_ref_contractive : Contractive interp_ref.
  Proof. solve_contractive. Qed.

  Program Definition interp_lit (v: base_lit) : (D -n> D) :=
    λne ii, match v return D with
            | LitInt _ | LitBool _ | LitUnit | LitPoison | LitProphecy _ => PersPred (λ _, True)                                                             
            | LitLoc _ => interp_ref ii
            end%I. 
  Final Obligation.
  intros []; solve_proper.
  Qed.

  Instance interp_lit_contractive v: Contractive (interp_lit v).
  Proof using. destruct v; solve_contractive. Qed.

  Program Definition interp_of (w : val heap_lang) : (D -n> D) :=
    λne ii, match w return D with
            | LitV v => interp_lit v ii
            | RecV _ _ _ => interp_arrow ii
            | PairV _ _ => interp_prod ii
            | InjLV _ | InjRV _ => interp_sum ii
      end%I.
  Final Obligation.
  Proof. intros []; try solve_proper. destruct l; solve_proper. 
  Qed.

  Instance interp_of_contractive w : Contractive (interp_of w).
  Proof.
    destruct w; cbn -[interp_arrow interp_prod interp_sum interp_ref]; apply (_ : Contractive _).
  Qed.

  Program Definition interp_one : D -n> D :=
    λne ii, PersPred (λ w, interp_of w ii w).
  Next Obligation.
  Proof.
    intros ???? w; cbn -[interp_of]; f_equiv; by apply contractive_ne; first apply _.
  Qed.
  Instance interp_one_contractive : Contractive interp_one.
  Proof.
    intros n ii ii' Hinterps w; cbn -[interp_of]; f_equiv; apply (_ : Contractive _); done.
  Qed.

  Definition interp : D := fixpoint interp_one.

  Lemma interp_unfold : interp ≡ interp_one interp.
  Proof. rewrite /interp; apply fixpoint_unfold. Qed.

  Definition interp_expr (τ: locale heap_lang) (e: expr heap_lang) : iProp Σ :=
    let _ := irisG_looping HeapLangEM si_add_none (lG := hG) in 
    pwp MaybeStuck CanFork ⊤ τ e interp.

  Definition interp_env (vs : gmap string (val heap_lang)) : iProp Σ :=
    [∗ map] _ ↦ v ∈ vs, interp v.

  Global Instance interp_env_persistent vs : Persistent (interp_env vs) := _.

  Lemma interp_env_Some_l vs s v :
    vs !! s = Some v → interp_env vs ⊢ interp v.
  Proof.
    iIntros (?) "Henv".
    iApply (big_sepM_lookup with "Henv"); eauto. 
  Qed.

  Lemma interp_env_nil : ⊢ interp_env ∅.
  Proof. rewrite /interp_env. set_solver. Qed.
  Lemma interp_env_cons vs s v (FRESH: s ∉ dom vs):
    interp_env (<[ s := v ]> vs) ⊣⊢ interp v ∗ interp_env vs.
  Proof.
    rewrite /interp_env.
    rewrite big_sepM_insert; [done| ].
    by apply not_elem_of_dom.
  Qed.

  Lemma interp_env_subseteq vs vs' (SUB: vs' ⊆ vs):
    interp_env vs -∗ interp_env vs'.
  Proof using.
    iIntros "#ENV". rewrite /interp_env.
    iApply big_sepM_subseteq; eauto.
  Qed.    

  Definition logrel (e : expr heap_lang) : iProp Σ :=
    □ ∀ vs τ, interp_env vs -∗ interp_expr τ (subst_env vs e).

End logrel.

Global Typeclasses Opaque interp_env.

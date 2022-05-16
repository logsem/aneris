From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.algebra Require Export monotone.
From aneris.lib Require Import gen_heap_light.

Definition gen_mono_heapUR (A : ofe) (R : relation A) :=
  authUR (monotoneUR R).

Class gen_mono_heapG L `{!EqDecision L} `{!Countable L} A R Σ := GenMonoHeapG {
  gen_mono_heapG_inG :> inG Σ (gen_mono_heapUR A R);
  gen_mono_heapG_names : gmap L gname;
}.

Class gen_mono_heapPreG L `{!EqDecision L} `{!Countable L} A R Σ := {
  gen_mono_heap_inPreG :> inG Σ (gen_mono_heapUR A R)
}.

Definition gen_mono_heapGΣ (A : ofe) (R : relation A) : gFunctors :=
    #[GFunctor (authUR (monotoneUR R))].

Global Instance subG_gen_mono_heapG {Σ} L `{!EqDecision L} `{!Countable L}
       (A : ofe) (R : relation A) :
  subG (gen_mono_heapGΣ A R) Σ → gen_mono_heapPreG L A R Σ.
Proof. solve_inG. Qed.

Section def.
  Context {L} `{!EqDecision L} `{!Countable L}.
  Context `{!gen_mono_heapG L A R Σ}.

  Definition Exact_def (l : L) (q : Qp) (v : A) : iProp Σ :=
    ∃ γ, ⌜gen_mono_heapG_names !! l = Some γ⌝ ∗ (own γ (●{#q} (principal R v)))%I.
  Definition Exact_aux : seal (Exact_def). by eexists. Qed.
  Definition Exact := Exact_aux.(unseal).
  Definition Exact_eq : Exact = Exact_def := Exact_aux.(seal_eq).

  Definition atleast_def (l : L) (v : A) : iProp Σ :=
    ∃ γ, ⌜gen_mono_heapG_names !! l = Some γ⌝ ∗ own γ (◯ (principal R v)).
  Definition atleast_aux : seal (atleast_def). by eexists. Qed.
  Definition atleast := atleast_aux.(unseal).
  Definition atleast_eq : atleast = atleast_def := atleast_aux.(seal_eq).
End def.

Notation "l ↦◯ v" := (atleast l v)
  (at level 20, format "l  ↦◯  v") : bi_scope.
Notation "l ↦●{ q } v" := (Exact l q%Qp v)
  (at level 20, q at level 50, format "l  ↦●{ q }  v") : bi_scope.
Notation "l ↦● v" := (Exact l 1 v)
  (at level 20, format "l  ↦●  v") : bi_scope.

Section gen_mono_heap.
  Context {L} `{!EqDecision L} `{!Countable L}.
  Context `{!gen_mono_heapG L A R Σ}.

  Global Instance Exact_fractional l v : Fractional (λ q, l ↦●{q} v)%I.
  Proof.
    intros p q. rewrite Exact_eq /Exact_def. iSplit.
    - iDestruct 1 as (γ) "(% & Ha)".
      iDestruct "Ha" as "[Ha1 Ha2]".
      iSplitL "Ha1"; eauto.
    - iDestruct 1 as "[Hp Hq]".
      iDestruct "Hp" as (?) "[% Hp]".
      iDestruct "Hq" as (?) "[% Hq]".
      simplify_map_eq. iCombine "Hp Hq" as "Hpq".
      eauto.
  Qed.
  Global Instance Exact_as_fractional l q v :
    AsFractional (l ↦●{q} v) (λ q, l ↦●{q} v)%I q.
  Proof. split; [done|]. apply _. Qed.
  Global Instance Exact_timeless l q v : Timeless (l ↦●{q} v).
  Proof. rewrite Exact_eq. apply _. Qed.

  Global Instance atleast_persistent l v : Persistent (l ↦◯ v).
  Proof. rewrite atleast_eq. apply _. Qed.
  Global Instance atleast_timeless l v : Timeless (l ↦◯ v).
  Proof. rewrite atleast_eq. apply _. Qed.

  Lemma mono_mapsto_related `{!PreOrder R} l q v1 v2 :
    l ↦●{q} v1 -∗ l ↦◯ v2 -∗ ⌜R v2 v1⌝.
  Proof.
    rewrite Exact_eq atleast_eq /Exact_def /atleast_def.
    iDestruct 1 as (γ) "[% Hs1]".
    iDestruct 1 as (γ') "[% Hs2]".
    simplify_eq.
    iDestruct (own_valid_2 with "Hs1 Hs2")
      as %(_ & Hvl & _)%auth_both_dfrac_valid_discrete; simpl in *.
    iPureIntro.
    by apply principal_included.
  Qed.

  Lemma mono_mapsto_update `{!Transitive R} l v1 v2 :
    R v1 v2 →
    l ↦● v1 ==∗ l ↦● v2 ∗ l ↦◯ v2.
  Proof.
    rewrite Exact_eq atleast_eq /Exact_def /atleast_def.
    iDestruct 1 as (γ) "[% HF]".
    iMod (own_update _ _ (● (principal _ v2) ⋅ ◯ (principal _ v2))
            with "HF") as "[HF Hf]".
    { apply auth_update_alloc. by apply monotone_local_update_grow. }
    iModIntro; iSplit; eauto.
  Qed.

  Lemma mono_mapsto_agree `{!(∀ n : nat, Proper (dist n ==> dist n ==> iff) R)}
      `{!Reflexive R} `{!AntiSymm (≡) R} l q1 q2 v1 v2 :
    l ↦●{q1} v1 -∗ l ↦●{q2} v2 -∗ v1 ≡ v2.
  Proof.
    rewrite Exact_eq /Exact_def.
    iDestruct 1 as (γ) "[% Hs1]".
    iDestruct 1 as (γ') "[% Hs2]".
    simplify_eq.
    iDestruct (own_valid_2 with "Hs1 Hs2") as %?%auth_auth_dfrac_op_inv.
    by iApply monotone_equivI.
  Qed.

End gen_mono_heap.

Lemma gen_mono_heap_init_pre `{!EqDecision L, !Countable L, !gen_mono_heapPreG L A R Σ}
      (X : gset L) (v : A) :
  ⊢ |==> ∃ (γs : gmap L gname),
      [∗ set] l ∈ X, ∃ γ, ⌜γs !! l = Some γ⌝ ∗
         own γ (● (principal R v)) ∗ own γ (◯ (principal R v)).
Proof.
  induction X as [|??? IH] using set_ind_L.
  { iIntros "!#". iExists ∅. by iApply big_sepS_empty. }
  iMod IH as "H". iDestruct "H" as (gX) "HX".
  iMod (own_alloc (● (principal R v) ⋅ ◯ (principal R v))) as (γ) "[HF Hf]".
  { by apply auth_both_valid. }
  iModIntro. iExists (<[x:=γ]>gX).
  rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
  iSplitR "HX"; last first.
  { iApply (big_sepS_impl with "HX").
    iIntros "!#" (??). iDestruct 1 as (?) "(%&?&?)".
    iExists _. rewrite lookup_insert_ne; [|set_solver]. by iFrame. }
  rewrite lookup_insert; eauto.
Qed.

Lemma gen_mono_heap_init `{!EqDecision L, !Countable L, !gen_mono_heapPreG L A R Σ}
      (X : gset L) (v : A) :
  ⊢ |==> ∃ _ : gen_mono_heapG L A R Σ, [∗ set] l ∈ X, l ↦● v ∗ l ↦◯ v.
Proof.
  iMod (gen_mono_heap_init_pre X v) as (γs) "H".
  iExists (GenMonoHeapG _ _ _ _ _ _ _ γs).
  rewrite Exact_eq atleast_eq /Exact_def /atleast_def.
  iApply (big_sepS_impl with "H").
  iIntros "!# !#" (??).
  iDestruct 1 as (?) "(% & HF & Hf)".
  iSplitL "HF"; eauto.
Qed.

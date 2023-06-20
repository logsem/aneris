From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap frac agree.
From iris.base_logic.lib Require Import gen_heap.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
Import uPred.

Section definitions.

  Definition gen_heapUR L `{!EqDecision L} `{!Countable L} V :=
    gmapUR L (prodR fracR (agreeR (leibnizO V))).

  Context `{Countable L, hG : !inG Σ (authR (gen_heapUR L V))}.

  Definition to_gen_heap (σ : gmap L V) : gmap L (frac * (agree (leibnizO V))) :=
    (λ v, (1%Qp, to_agree v)) <$> σ.

  Lemma lookup_to_gen_heap_None σ l :
    σ !! l = None → to_gen_heap σ !! l = None.
  Proof. rewrite /to_gen_heap lookup_fmap => ->//. Qed.

  Lemma to_gen_heap_insert σ l v :
    to_gen_heap (<[l := v]>σ) = <[ l := (1%Qp, to_agree v)]>(to_gen_heap σ).
  Proof. rewrite /to_gen_heap fmap_insert //. Qed.

  Lemma to_gen_heap_valid σ : ✓ (to_gen_heap σ).
  Proof. intros i; rewrite lookup_fmap; destruct (σ !! i); done. Qed.

  Lemma gen_heap_singleton_included σ l q v :
    {[ l := (q, to_agree v)]} ≼ to_gen_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l; intros (w & Hw1 & Hw2).
    revert Hw2; rewrite -Hw1; clear Hw1.
    rewrite /to_gen_heap lookup_fmap; clear w.
    intros [|(w & w' & Hw1 & Hw2 & Hw3)]%option_included; first done.
    destruct (σ !! l); last by inversion Hw2.
    simplify_eq/=.
    destruct Hw3 as [[_ ->%(@to_agree_inj)%leibniz_equiv]|Hw3]; first done.
    apply prod_included in Hw3 as [_ ->%(@to_agree_included)%leibniz_equiv];
      done.
  Qed.

  Definition gen_heap_light_ctx (γ : gname) (σ : gmap L V) : iProp Σ :=
    @own _ _ hG γ (● (to_gen_heap σ)).

  Definition lmapsto_def (γ : gname) (l : L) (q : Qp) (v: V) : iProp Σ :=
    own γ (◯ {[ l := (q, to_agree (v : leibnizO V)) ]}).
  Definition lmapsto_aux : seal (@lmapsto_def). Proof. by eexists. Qed.
  Definition lmapsto := lmapsto_aux.(unseal).
  Definition lmapsto_eq : @lmapsto = @lmapsto_def := lmapsto_aux.(seal_eq).
End definitions.

Local Notation "l ; γ ↦{ q } v" := (lmapsto γ l q v)
  (at level 20, q at level 50, format "l  ;  γ  ↦{ q }  v") : bi_scope.
Local Notation "l ; γ ↦ v" := (lmapsto γ l 1 v) (at level 20) : bi_scope.

Local Notation "l ; γ ↦{ q } -" := (∃ v, l ; γ ↦{q} v)%I
  (at level 20, q at level 50, format "l  ;  γ  ↦{ q }  -") : bi_scope.
Local Notation "l ; γ ↦ -" := (l ; γ ↦{1} -)%I (at level 20) : bi_scope.

Section gen_heap_light.
  Context {L V} `{Countable L, !inG Σ (authR (gen_heapUR L V))}.
  Implicit Types σ : gmap L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of lmapsto *)
  Global Instance lmapsto_timeless l γ q v : Timeless (l ; γ ↦{q} v).
  Proof. rewrite lmapsto_eq /lmapsto_def. apply _. Qed.
  Global Instance lmapsto_fractional l γ v : Fractional (λ q, l ; γ ↦{q} v)%I.
  Proof.
    intros p q. by rewrite lmapsto_eq /lmapsto_def -own_op -auth_frag_op
      singleton_op -pair_op agree_idemp.
  Qed.
  Global Instance lmapsto_as_fractional l γ q v :
    AsFractional (l ; γ ↦{q} v) (λ q, l ; γ ↦{q} v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma gen_heap_light_init σ :
    ⊢ |==> ∃ (γ : gname), gen_heap_light_ctx γ σ.
  Proof.
    iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
    { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
    eauto.
  Qed.

  Lemma lmapsto_agree l γ q1 q2 v1 v2 :
    l ; γ ↦{q1} v1 -∗ l ; γ ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite lmapsto_eq /lmapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv. rewrite auth_frag_valid singleton_op singleton_valid -pair_op.
    intros [_ ?%to_agree_op_inv_L]; done.
  Qed.

  Lemma lmapsto_combine l γ q1 q2 v1 v2 :
    l ; γ ↦{q1} v1 -∗ l ; γ ↦{q2} v2 -∗ l ; γ ↦{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (lmapsto_agree with "Hl1 Hl2") as %->.
    iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Global Instance frame_lmapsto p γ l v q1 q2 RES :
    FrameFractionalHyps p (l ; γ ↦{q1} v) (λ q, l ; γ ↦{q} v)%I RES q1 q2 →
    Frame p (l ; γ ↦{q1} v) (l ; γ ↦{q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance ex_lmapsto_fractional l γ : Fractional (λ q, l ; γ ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (lmapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance ex_lmapsto_as_fractional l γ q :
    AsFractional (l ; γ ↦{q} -) (λ q, l ; γ ↦{q} -)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma lmapsto_valid l γ q v : l ; γ ↦{q} v -∗ ✓ q.
  Proof.
    rewrite lmapsto_eq /lmapsto_def own_valid !discrete_valid auth_frag_valid.
    apply pure_mono=> /singleton_valid [??]; done.
  Qed.
  Lemma lmapsto_valid_2 l γ q1 q2 v1 v2 :
    l ; γ ↦{q1} v1 -∗ l ; γ ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (lmapsto_agree with "H1 H2") as %->.
    iApply (lmapsto_valid l _ _ v2). by iFrame.
  Qed.

  Lemma lmapsto_lmapsto_ne l1 l2 γ q1 q2 v1 v2 :
    ¬ ✓(q1 + q2)%Qp → l1 ; γ ↦{q1} v1 -∗ l2 ; γ ↦{q2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros (?) "Hl1 Hl2"; iIntros (->).
    by iDestruct (lmapsto_valid_2 with "Hl1 Hl2") as %?.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_light_alloc σ l γ v :
    σ !! l = None →
    gen_heap_light_ctx γ σ ==∗ gen_heap_light_ctx γ (<[l:=v]>σ) ∗ l ; γ ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_light_ctx lmapsto_eq /lmapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iModIntro.
    rewrite to_gen_heap_insert. iFrame.
  Qed.

  Lemma gen_heap_light_alloc_gen σ σ' γ :
    σ' ##ₘ σ →
    gen_heap_light_ctx γ σ ==∗
    gen_heap_light_ctx γ (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ; γ ↦ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_light_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma gen_heap_light_valid σ l γ q v :
    gen_heap_light_ctx γ σ -∗ l ; γ ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_light_ctx lmapsto_eq /lmapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[?%gen_heap_singleton_included _]%auth_both_valid_discrete; auto.
  Qed.

  Lemma gen_heap_light_update γ σ l v1 v2 :
    gen_heap_light_ctx γ σ -∗ l ; γ ↦ v1 ==∗
    gen_heap_light_ctx γ (<[l:=v2]>σ) ∗ l ; γ ↦ v2.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_light_ctx lmapsto_eq /lmapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (v2:leibnizO _)))=> //.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iModIntro. iFrame "Hl". rewrite to_gen_heap_insert. iFrame.
  Qed.

  Lemma gen_heap_light_init_strong σ :
    ⊢ |==> ∃ γ, gen_heap_light_ctx γ σ ∗ 
                [∗ map] l ↦ v ∈ σ, lmapsto γ l 1 v.
  Proof.
    iInduction σ as [|σ Hnin] "IHσ" using map_ind.
    { iMod (gen_heap_light_init ∅) as (γ) "Hγ".
      iExists γ. rewrite big_sepM_empty. by iFrame. }
    iMod "IHσ" as (γ) "[Hσ Hσs]".
    iMod (gen_heap_light_alloc with "Hσ") as "[Hσ Hs]"; [done|].
    iModIntro. iExists γ. rewrite big_sepM_insert; [|done]. by iFrame.
  Qed.

End gen_heap_light.

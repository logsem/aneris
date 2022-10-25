From iris.proofmode Require Import tactics.
From aneris.algebra Require Import monotone.
From iris.algebra Require Import agree gmap auth excl numbers frac_auth.
From aneris.aneris_lang Require Import resources.
From aneris.examples.reliable_communication.resources Require Export prelude.

Set Default Proof Using "Type".

Section SeqIdResources.
  Context `{A : ofe}.
  Context `{!anerisG Mdl Σ, !ChanMsgHist A Σ}.
  Context (γlbuf: chan_logbuf_name).

  Notation γlst := (chan_logbuf_buf_name γlbuf).
  Notation γcpt := (chan_logbuf_cpt_name γlbuf).

  (* Parameter frag_list : ∀ T, gname → (nat * T) → iProp Σ. *)
  Definition frag_list (n : nat) (a : A) : iProp Σ :=
    ∃ (l : listO A), own γlst (◯ PrinCMH l) ∗ ⌜l !! n = Some a⌝.

  (* Parameter auth_list : ∀ T, gname → list T → iProp Σ. *)
  Definition auth_list (l : list A) : iProp Σ :=
    own γlst (● PrinCMH l) ∗ own γcpt (●F (length l)) ∗
    [∗ list] i ↦ x ∈ l, frag_list i x.

  (* Parameter alloc_at : gname → nat → iProp Σ. *)
  Definition alloc_at (n : nat) : iProp Σ := own γcpt (◯F{1} n).

  (* Definition frag_list_exists γ i : iProp Σ := ∃ {T} (x:T), frag_list γ (i,x). *)
  Definition frag_list_exists n : iProp Σ := ∃ v, frag_list n v.

  (* Axiom frag_list_persistent : ∀ {T} γ (p:nat * T), Persistent (frag_list γ p). *)
  Instance frag_list_persistent n v : Persistent (frag_list n v).
  Proof. apply _. Qed.

  (* Instance frag_list_exists_persistent {T} γ (p:nat * T) : Persistent (frag_list γ p).*)
  Instance frag_list_exists_persistent n : Persistent (frag_list_exists n).
  Proof. apply _. Qed.


  Lemma alloc_at_excl n n' :
    alloc_at n ⊢ alloc_at n' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    by apply frac_auth_frag_op_valid in Hvl as [Hvl _].
  Qed.

  (* Axiom auth_list_agree : ∀ {T} γ (xs : list T) n (x : T),
    auth_list γ xs ∗ frag_list γ (n,x) -∗ ⌜nth_error xs n = Some x⌝. *)
  Lemma auth_list_agree xs n x :
    auth_list xs ⊢ frag_list n x -∗ ⌜xs !! n = Some x⌝.
  Proof.
    iIntros "[HauthL ?] HfragL".
    iDestruct "HfragL" as (ys) "(HfragL & %Heq)".
    iDestruct (own_valid_2 with "HauthL HfragL") as %[Hsubl _]%auth_both_valid_discrete.
    rewrite principal_included in Hsubl. destruct Hsubl as (zs & ->).
    rewrite lookup_app_l; [done|].
    by apply lookup_lt_is_Some_1.
  Qed.

  Lemma auth_list_agree_2 xs n x :
    xs !! n = Some x → auth_list xs -∗ frag_list n x.
  Proof.
    iIntros (Hlookup) "(Hauth & Hcpt & #Hfrags)".
    iDestruct (big_sepL_insert_acc with "Hfrags") as "[Hfrag _]"; [done|].
    iFrame "#∗".
  Qed.

  (* Axiom auth_list_extend : ∀ {T:Type} γ xs (x : T) n,
    auth_list γ xs ∗ alloc_at γ n ==∗
    auth_list γ (xs ++ [x]) ∗ alloc_at γ (S n) ∗
    frag_list γ (n,x). *)
  Lemma auth_list_extend xs x n :
    auth_list xs ⊢ alloc_at n ==∗
    auth_list (xs ++ [x]) ∗ alloc_at (S n) ∗ frag_list n x.
  Proof.
    iIntros "[HauthL [HauthC #HfragsC]] HfragC".
    rewrite /alloc_at /frag_list.
    iMod (own_update γlst _
                     (● PrinCMH (xs ++ [x]) ⋅ ◯ PrinCMH (xs ++ [x]))
           with "[$HauthL]") as "[HauthL #HfragL]".
    - apply auth_update_alloc.
      apply monotone_local_update_grow.
      by apply prefix_app_r.
    - iAssert (⌜length xs = n⌝%I) with "[HauthC HfragC]" as %Heq.
      { destruct γlbuf. simplify_eq /=.
        by iDestruct (own_valid_2 with "HauthC HfragC") as
        %Heq%frac_auth_agree_L. }
      iMod (own_update_2 γcpt _ _ ((●F (S n)) ⋅ ◯F{1} (S n))
             with "[$HauthC] [$HfragC]") as "[HauthC HfragC]".
      + apply frac_auth_update, (nat_local_update _ _ (S _) (S _)). lia.
      + rewrite -Heq -(last_length _ x).
        iFrame "#∗". iModIntro.
        rewrite big_sepL_singleton.
        iSplitL.
        { iExists _. iFrame "#". iPureIntro. subst.
          rewrite lookup_app_r;
            [by replace (length xs + 0 - length xs) with 0 by lia| lia]. }
        iExists _. iFrame "#".
        iPureIntro.
        rewrite lookup_app_r;
            [by replace (length xs - length xs) with 0 by lia| lia].
  Qed.

  Lemma auth_list_length xs n :
    auth_list xs ⊢ alloc_at n -∗ ⌜length xs = n⌝.
  Proof.
    iIntros "[Hauth [Halloc_auth _]] Halloc_frag".
    iDestruct (own_valid_2 with "Halloc_auth Halloc_frag") as %H.
    by apply frac_auth_agree_L in H.
  Qed.

  Global Instance auth_list_timeless xs : Timeless (auth_list xs).
  Proof. apply _. Qed.


End SeqIdResources.

Section SeqIdResourcesAlloc.
  Context `{A : ofe}.
  Context
 `{!anerisG Mdl Σ, !ChanMsgHist A Σ}.

  (* Axiom auth_list_alloc :
     ∀ {T:Type}, ⊢ (|==> ∃ γ, @auth_list T γ [] ∗ alloc_at γ 0)%I. *)
  Lemma auth_list_alloc :
    True ⊢ |==> ∃ γlbuf, auth_list γlbuf [] ∗ alloc_at γlbuf 0.
  Proof.
    rewrite /auth_list /alloc_at.
    iIntros (_).
    iMod (own_alloc (● (PrinCMH []))) as (γlst) "HauthL";
      first by apply auth_auth_valid.
    iMod (own_alloc (●F 0 ⋅ ◯F 0)) as (γcpt) "[HauthC HfragC]";
      first by apply auth_both_valid_discrete.
    iExists (ChanLogBufName γlst γcpt).
    eauto with iFrame.
  Qed.

End SeqIdResourcesAlloc.

Section SeqIdResourcesUtil.
  Context `{A : ofe}.
  Context `{!anerisG Mdl Σ, !ChanMsgHist A Σ}.

  Lemma prefix_frag_list γl γr l r i v :
    r `prefix_of` l → i < length r →
    auth_list γl l -∗ auth_list γr r -∗ frag_list γl i v -∗
    frag_list γr i v.
  Proof.
    iIntros ([k ->] Hlen) "Hauthl Hauthr Hfragl".
    iDestruct (auth_list_agree with "Hauthl Hfragl") as %Hnth.
    rewrite lookup_app_l in Hnth; [|done].
    iDestruct (auth_list_agree_2 with "Hauthr") as "Hfragr"; [done|].
    by iFrame.
  Qed.

  (* TODO: Deprecated - Remove? *)
  (* Lemma our_awesome_lemma3 γl γr l r n v w : *)
  (*    l = r ++ [w] → *)
  (*    auth_list γl l -∗ *)
  (*    auth_list γr r -∗ frag_list γl n v -∗ *)
  (*    alloc_at γr n ==∗ *)
  (*    auth_list γl l ∗ auth_list γr (r ++ [w]) ∗ *)
  (*    alloc_at γr (S n) ∗ frag_list γr n w. *)
  (*  Proof. *)
  (*    iIntros (Heq) "Hauthl Hauthr Hfragl Hat". *)
  (*    iMod (auth_list_extend with "Hauthr Hat") as "(Hauth & Hat & Hfragr)". *)
  (*    iModIntro. iFrame. *)
  (*  Qed. *)

End SeqIdResourcesUtil.

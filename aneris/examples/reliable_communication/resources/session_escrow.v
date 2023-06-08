From iris.bi Require Import updates.
From iris.algebra Require Import agree gmap auth excl numbers frac_auth csum.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre step_update.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From aneris.examples.reliable_communication.resources
     Require Export mono_list step_proto.

Set Default Proof Using "Type".

(** Side switch. *)
Definition dual_side (s : side) : side := side_elim s Right Left.

Record session_escrow_name :=
  SessionEscrowName {
      session_escrow_proto_name : proto_name;
      session_escrow_Tl_name : gname;
      session_escrow_Tr_name : gname;
      session_escrow_sl_name : gname;
      session_escrow_rl_name : gname;
      session_escrow_sr_name : gname;
      session_escrow_rr_name : gname
    }.

Global Instance session_escrow_name_inhabited : Inhabited session_escrow_name :=
  populate (SessionEscrowName inhabitant inhabitant inhabitant inhabitant inhabitant inhabitant inhabitant).
Global Instance session_escrow_name_eq_dec : EqDecision session_escrow_name.
Proof. solve_decision. Qed.
Global Instance session_escrow_name_countable : Countable session_escrow_name.
Proof.
  refine (inj_countable
            (λ '(SessionEscrowName γp γ_Tl γ_Rl γ_sl γ_rl γ_sr γ_rr),
               (γp, γ_Tl, γ_Rl, γ_sl, γ_rl, γ_sr, γ_rr))
            (λ '(γp, γ_Tl, γ_Rl, γ_sl, γ_rl, γ_sr, γ_rr),
               Some (SessionEscrowName γp γ_Tl γ_Rl γ_sl γ_rl γ_sr γ_rr)) _);
    by intros [].
Qed.

Class session_escrowG Σ V := {
    session_escrowG_protoG :> protoG Σ V;
    session_escrowG_histG :> inG Σ (mono_listUR (leibnizO V));
    session_escrowG_counterG :> inG Σ (excl_authR natO);
  }.

Definition session_escrowΣ V : gFunctors :=
  #[protoΣ V; GFunctor (mono_listUR (leibnizO V)); GFunctor (excl_authR natO)].

Global Instance subG_session_escrowΣ V {Σ} :
  subG (session_escrowΣ V) Σ → session_escrowG Σ V.
Proof. solve_inG. Qed.

Section iProto_sessions.
  Context `{A : Type}.
  Context `{!session_escrowG Σ A, !anerisG Mdl Σ}.
  Context (N : namespace).

  Definition auth_list (χ : session_escrow_name) (s : side) (xs : list A) :=
    own (side_elim s (χ.(session_escrow_Tl_name)) (χ.(session_escrow_Tr_name)))
        (●ML (xs : list (leibnizO A))).
  Definition frag_list (χ : session_escrow_name) (s : side) (n : nat) (x : A) : iProp Σ :=
    ∃ xs, ⌜xs !! n = Some x⌝ ∗
          own (side_elim s (χ.(session_escrow_Tl_name))
                         (χ.(session_escrow_Tr_name)))
              (◯ML (xs : list (leibnizO A))).

Definition auth_auth_sent (χ : session_escrow_name) (s : side) (n : nat) : iProp Σ :=
    own (side_elim s χ.(session_escrow_sl_name) χ.(session_escrow_sr_name))
        (●E n).
  Definition auth_frag_sent (χ : session_escrow_name) (s : side) (n : nat) : iProp Σ :=
    own (side_elim s χ.(session_escrow_sl_name) χ.(session_escrow_sr_name))
        (◯E n).
  Definition auth_auth_recv (χ : session_escrow_name) (s : side) (n : nat) : iProp Σ :=
    own (side_elim s χ.(session_escrow_rl_name) χ.(session_escrow_rr_name))
        (●E n).
  Definition auth_frag_recv (χ : session_escrow_name) (s : side) (n : nat) : iProp Σ :=
    own (side_elim s χ.(session_escrow_rl_name) χ.(session_escrow_rr_name))
        (◯E n).

  Definition Ses_inv (χ : session_escrow_name) : iProp Σ :=
    ∃ (Tl Tr : list A) (nl nr : nat),
      ⌜nr ≤ length Tl⌝ ∗ ⌜nl ≤ length Tr⌝ ∗
      iProto_step_ctx χ.(session_escrow_proto_name) (drop nr Tl) (drop nl Tr) ∗
      auth_list χ Left Tl ∗ auth_list χ Right Tr ∗
      auth_auth_sent χ Left (length Tl) ∗ auth_auth_recv χ Left nl ∗
      auth_auth_sent χ Right (length Tr) ∗ auth_auth_recv χ Right nr.

  Definition Ses (χ : session_escrow_name) : iProp Σ :=
    inv N (Ses_inv χ).

  Definition ses_own_def (χ : session_escrow_name) (s : side) (n m : nat) (p : iProto Σ A) : iProp Σ :=
    Ses χ ∗
    iProto_own χ.(session_escrow_proto_name) s p ∗
    auth_frag_sent χ s n ∗ auth_frag_recv χ s m.
  Definition ses_own_aux : seal (ses_own_def). by eexists. Qed.
  Definition ses_own := ses_own_aux.(unseal).
  Definition ses_own_eq : @ses_own = @ses_own_def := ses_own_aux.(seal_eq).
  Global Instance: Params (@ses_own) 5 := {}.

  Global Instance ses_own_contractive χ s n m : Contractive (ses_own χ s n m).
  Proof. rewrite ses_own_eq. solve_contractive. Qed.
  Global Instance ses_own_ne χ s n m : NonExpansive (ses_own χ s n m).
  Proof. rewrite ses_own_eq. solve_proper. Qed.
  Global Instance ses_own_proper χ s n m : Proper ((≡) ==> (≡)) (ses_own χ s n m).
  Proof. rewrite ses_own_eq. solve_proper. Qed.

  Definition ses_idx_def (χ : session_escrow_name) (s : side) (n : nat) (x : A) :=
    frag_list χ s n x.
  Definition ses_idx_aux : seal (ses_idx_def). by eexists. Qed.
  Definition ses_idx := ses_idx_aux.(unseal).
  Definition ses_idx_eq : @ses_idx = @ses_idx_def := ses_idx_aux.(seal_eq).
  Global Instance: Params (@ses_idx) 4 := {}.

  Global Instance ses_idx_contractive χ s n v : Persistent (ses_idx χ s n v).
  Proof. rewrite ses_idx_eq. apply _. Qed.

  Lemma ses_own_le χ s n m p1 p2 :
    ses_own χ s n m p1 -∗ ▷ (p1 ⊑ p2) -∗ ses_own χ s n m p2.
  Proof.
    rewrite ses_own_eq.
    iIntros "(Hinv & Hp & H) Hle".
    iDestruct (iProto_own_le with "Hp Hle") as "Hp". by iFrame.
  Qed.

  (* Have this lemma to make it consistent with the others of the ghost theory. *)
  Lemma step_get_Ses_init E p :
    ⊢ |~{E}~| ∃ χ, Ses χ ∗ ses_own χ Left 0 0 p ∗
                   ses_own χ Right 0 0 (iProto_dual p).
  Proof.
    iApply step_get_impl; [iApply step_get_lb_get|].
    iIntros "#Hsteps".
    iApply step_get_impl; [iApply (iProto_step_init E p)|].
    iDestruct 1 as (γc) "(Hctx & Hpl & Hpr)".
    iMod (own_alloc (●ML [])) as (γl) "Hl"; [apply mono_list_auth_valid|].
    iMod (own_alloc (●ML [])) as (γr) "Hr"; [apply mono_list_auth_valid|].
    iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γsl) "[HslA HslF]"; [apply excl_auth_valid|].
    iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γrl) "[HrlA HrlF]"; [apply excl_auth_valid|].
    iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γsr) "[HsrA HsrF]"; [apply excl_auth_valid|].
    iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γrr) "[HrrA HrrF]"; [apply excl_auth_valid|].
    set (χ := SessionEscrowName γc γl γr γsl γrl γsr γrr).
    iMod (inv_alloc N E (Ses_inv χ) with "[Hctx Hl Hr HslA HrlA HsrA HrrA]")
      as "#H".
    { iIntros "!>". iExists [], [], 0%nat, 0%nat. iFrame.
      iSplit; iPureIntro; lia. }
    iIntros (n) "Hauth". iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". iFrame. iMod "Hclose".
    iModIntro.
    iExists χ.
    rewrite !ses_own_eq.
    iFrame "#∗".
  Qed.

  Lemma step_update_send χ s E n m pm v p :
    ↑N ⊆ E →
    ses_own χ s n m (<!> pm)%proto -∗ iMsg_car pm v (Next p) -∗
    |~{E}~> (ses_own χ s (S n) m p ∗ ses_idx χ s n v).
  Proof.
    rewrite ses_own_eq ses_idx_eq.
    iIntros (HE) "[#HI (Hp&HsF&HrF)] Hpm".
    iApply step_update_open.
    iInv N as "H" "Hclose".
    iDestruct "H" as (Tl Tr nl nr)
                       "(>%Hle&>%Hle2&Hctx&>HTl&>HTr&>Hsl&>Hrl&>Hsr&>Hrr)".
    destruct s.
    - iApply (step_update_impl with "[Hctx Hp Hpm]");
        [iApply (iProto_step_send_l with "Hctx Hp Hpm")|].
      iModIntro.
      iApply step_update_intro; [set_solver|].
      iIntros "[Hctx Hp]".
      iDestruct (own_valid_2 with "Hsl HsF") as %Hvalid1%excl_auth_agree_L.
      iDestruct (own_valid_2 with "Hrl HrF") as %Hvalid2%excl_auth_agree_L.
      iMod (own_update_2 _ _ _ (●E (S (length Tl)) ⋅ ◯E (S (length Tl)))
             with "Hsl HsF") as "[Hsl HsF]"; [by apply excl_auth_update|].
      iMod (own_update _ _ (●ML ((Tl ++ [v]):list (leibnizO A)))
             with "HTl") as "HTl".
      { apply mono_list_update. by apply prefix_app_r. }
      rewrite mono_list_auth_lb_op.
      iDestruct "HTl" as "[HTl HTl']".
      iAssert (frag_list χ Left n v) with "[HTl']" as "Hidx".
      { iExists _. iFrame. iPureIntro. rewrite -Hvalid1.
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. done. }
      rewrite Hvalid1.
      iFrame "#∗".
      iApply "Hclose".
      iIntros "!>".
      rewrite -drop_app_le; [|lia].
      iExists (Tl ++ [v]), Tr, nl, nr.
      rewrite app_length. rewrite Hvalid1. simpl.
      replace (S n) with (n + 1)%nat by lia.
      iFrame.
      iSplit; iPureIntro; lia.
    - iApply (step_update_impl with "[Hctx Hp Hpm]");
        [iApply (iProto_step_send_r with "Hctx Hp Hpm")|].
      iModIntro.
      iApply step_update_intro; [set_solver|].
      iIntros "[Hctx Hp]".
      iDestruct (own_valid_2 with "Hsr HsF") as %Hvalid1%excl_auth_agree_L.
      iDestruct (own_valid_2 with "Hrr HrF") as %Hvalid2%excl_auth_agree_L.
      iMod (own_update_2 _ _ _ (●E (S (length Tr)) ⋅ ◯E (S (length Tr)))
             with "Hsr HsF") as "[Hs HsF]"; [by apply excl_auth_update|].
      iMod (own_update _ _ (●ML ((Tr ++ [v]):list (leibnizO A)))
             with "HTr") as "HTr".
      { apply mono_list_update. by apply prefix_app_r. }
      rewrite mono_list_auth_lb_op.
      iDestruct "HTr" as "[HTr HTr']".
      iAssert (frag_list χ Right n v) with "[HTr']" as "Hidx".
      { iExists _. iFrame. iPureIntro. rewrite -Hvalid1.
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. done. }
      rewrite Hvalid1.
      iFrame "#∗".
      iApply "Hclose".
      iIntros "!>".
      rewrite -drop_app_le; [|lia].
      iExists Tl, (Tr ++ [v]), nl, nr.
      rewrite app_length. rewrite Hvalid1. simpl.
      replace (S n) with (n + 1)%nat by lia.
      iFrame "#∗".
      iSplit; iPureIntro; lia.
  Qed.

  Lemma step_update_recv_l χ E n m pm v :
    ↑N ⊆ E →
    ses_own χ Left n m (<?> pm)%proto -∗ ses_idx χ Right m v -∗
    |~{E}~> ∃ p, ses_own χ Left n (S m) p ∗ iMsg_car pm v (Next p).
  Proof.
    rewrite !ses_own_eq !ses_idx_eq.
    iIntros (HE) "[#HI (Hp&HslF&HrlF)] Hidx".
    iApply step_update_open.
    iInv N as "H" "Hclose".
    iDestruct "H" as (Tl Tr nl nr)
                       "(>%Hle&>%Hle2&Hctx&>HTl&>HTr&>Hsl&>Hrl&>Hsr&>Hrr)".
    iDestruct (own_valid_2 with "Hrl HrlF") as %Hvalid%excl_auth_agree_L.
    rewrite Hvalid.
    iDestruct "Hidx" as (Tr') "[%Hlookup HTr']".
    iDestruct (own_valid_2 with "HTr HTr'") as %Hvalid'%mono_list_both_valid_L.
    destruct Hvalid' as [Tr'' ->].
    assert (m < length Tr')%nat as Hm.
    { by eapply (lookup_lt_Some Tr' m). }
    rewrite drop_app_le; last first.
    { by apply Nat.lt_le_incl. }
    rewrite (drop_S Tr' v m); [|done]=> /=.
    iModIntro.
    iApply (step_update_impl with "[Hctx Hp]");
      [iApply (iProto_step_recv_l with "Hctx Hp")|].
    iApply step_update_intro; [set_solver|].
    iDestruct 1 as (p) "(Hctx & Hp &HP)".
    iMod (own_update_2 _ _ _ (●E (S m) ⋅ ◯E (S m))
           with "Hrl HrlF") as "[Hrl HrlF]"; [by apply excl_auth_update|].
    destruct Tr' as [|r Tr']; [done|]=> /=.
    iMod ("Hclose" with "[-Hp HP HslF HrlF]") as "_".
    { iNext. iExists Tl,((r::Tr')++Tr''),(S m),nr. iFrame "#∗".
      rewrite drop_app_le; last first.
      { rewrite -Nat.lt_succ_r. apply le_n_S. done. }
      iFrame.
      iSplit; iPureIntro.
      - done.
      - rewrite app_length.
        etransitivity. apply Hm.
        apply Nat.le_add_r. }
    iModIntro. iFrame "#∗".
    iExists p. iFrame.
  Qed.

  Lemma step_update_recv_r χ E n m pm v :
    ↑N ⊆ E →
    ses_own χ Right n m (<?> pm)%proto -∗ ses_idx χ Left m v -∗
    |~{E}~> ∃ p, ses_own χ Right n (S m) p ∗ iMsg_car pm v (Next p).
  Proof.
    rewrite !ses_own_eq !ses_idx_eq.
    iIntros (HE) "[#HI (Hp&HsrF&HrrF)] Hidx".
    iApply step_update_open.
    iInv N as "H" "Hclose".
    iDestruct "H" as (Tl Tr nl nr)
                       "(>%Hle&>%Hle2&Hctx&>HTl&>HTr&>Hsl&>Hrl&>Hsr&>Hrr)".
    iDestruct (own_valid_2 with "Hrr HrrF") as %Hvalid%excl_auth_agree_L.
    rewrite Hvalid.
    iDestruct "Hidx" as (Tl') "[%Hlookup HTl']".
    iDestruct (own_valid_2 with "HTl HTl'") as %Hvalid'%mono_list_both_valid_L.
    destruct Hvalid' as [Tl'' ->].
    assert (m < length Tl')%nat as Hm.
    { by eapply (lookup_lt_Some Tl' m). }
    rewrite drop_app_le; last first.
    { by apply Nat.lt_le_incl. }
    rewrite (drop_S Tl' v m); [|done]=> /=.
    iModIntro.
    iApply (step_update_impl with "[Hctx Hp]");
      [iApply (iProto_step_recv_r with "Hctx Hp")|].
    iApply step_update_intro; [set_solver|].
    iDestruct 1 as (p) "(Hctx & Hp &HP)".
    iMod (own_update_2 _ _ _ (●E (S m) ⋅ ◯E (S m))
           with "Hrr HrrF") as "[Hrr HrrF]"; [by apply excl_auth_update|].
    simpl.
    destruct Tl' as [|l Tl']; [done|]=> /=.
    iMod ("Hclose" with "[-Hp HP HsrF HrrF]") as "_".
    { iNext. iExists ((l::Tl')++Tl''),Tr,nl,(S m). iFrame "#∗".
      rewrite drop_app_le; last first.
      { rewrite -Nat.lt_succ_r. apply le_n_S. done. }
      iFrame.
      iSplit; iPureIntro.
      - rewrite app_length.
        etransitivity. apply Hm.
        apply Nat.le_add_r.
      - done. }
    iModIntro. iFrame "#∗".
    iExists p. iFrame.
  Qed.

  (* TODO: Unify the proof of the above rules into this one. *)
  Lemma step_update_recv χ s E n m pm v :
    ↑N ⊆ E →
    ses_own χ s n m (<?> pm)%proto -∗ ses_idx χ (dual_side s) m v -∗
    |~{E}~> ∃ p, ses_own χ s n (S m) p ∗ iMsg_car pm v (Next p).
  Proof.
    iIntros (HE) "Hp Hpm".
    destruct s.
    - by iApply (step_update_recv_l with "Hp Hpm").
    - by iApply (step_update_recv_r with "Hp Hpm").
  Qed.

End iProto_sessions.

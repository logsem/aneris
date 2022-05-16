From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib Require Import pers_socket_proto lock_proof monitor_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From stdpp Require Import base tactics telescopes.
From aneris.examples.reliable_communication Require Import client_server_code.
From aneris.examples.reliable_communication.resources Require Import chan_endpoints_resources.

Section Proof_of_send.
  Context `{!anerisG Mdl Σ,
            !chanG Σ,
            !lockG Σ,
            !server_ghost_names}.

  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma send_spec_internal γe (c : val) v p ip serA :
    {{{ c ↣{ γe, ip, serA } (<!> MSG v; p)%proto ∗ ⌜Serializable serA v⌝ }}}
      send c v @[ip]
    {{{ RET #(); c ↣{ γe, ip, serA } p }}}.
  Proof.
    iIntros (Φ) "(Hc & %Hser) HΦ".
    rewrite iProto_mapsto_eq.
    iDestruct "Hc" as (γs s ser _serf sa dst) "Hc".
    iDestruct "Hc"
      as (sbuf slk rbuf rlk sidLBLoc ackIdLoc sidx ridx -> Heqc) "(%Heqg & Hc)".
    iDestruct "Hc"
      as "(Hl & %Hleq & HT_at & HR_at & Hsidx & Hridx
                 & #HsnT & #HaT & #HsT & #HidxsT
                 & Hp & #Hslk & #Hrlk & #Hinv)".
    wp_lam.
    wp_pures.
    wp_apply (monitor_acquire_spec with "Hslk").
    iIntros (v') "(-> & Hlocked & Hlk)".
    iDestruct "Hlk" as (q vs sidLB) "(Hsbuf & %Hq & HsidLBLoc' & Hsidx' & Hvs)".
    wp_pures.
    wp_load. wp_pures.
    wp_apply (wp_queue_add); [done|].
    iIntros (rv Hq').
    wp_pure _.
    wp_bind (Store _ _).
    iInv (chan_N (endpoint_chan_name γe)) as "IH".
    iDestruct "IH" as (Tl Tr Rl Rr) "(HTl & HTr & HRl & HRr & IH)".
    iDestruct "IH" as "(>%Hpre1 & >%Hpre2 & >#Hlbl & >#Hlbr & Hctx)".
    simplify_eq.
    iDestruct (mono_nat_auth_own_agree with "Hsidx Hsidx'") as %[_ ->].
    (* TODO: Fix weird split behaviour *)
    iMod (mono_nat_own_update (sidLB + length vs + 1) with "[Hsidx Hsidx']")
      as "[Hsidx _]";
      [|iApply fractional_half;
         [apply mono_nat_auth_own_as_fractional|iFrame]|]; [lia|].
    iDestruct "Hsidx" as "[Hsidx Hsidx']".
    destruct s.
    - iApply (aneris_wp_lb_step with "Hlbr [Hctx Hp]"); [done| |].
      { iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
        iIntros "!>!>".
        iMod (iProto_send_l with "Hctx Hp []") as "[Hctx Hp]".
        { rewrite iMsg_base_eq /=; auto. }
        iApply step_fupdN_intro; [done|].
        iIntros "!>". iApply (bi.laterN_le (length (list_minus Tr Rl)));
          [rewrite list_minus_prefix_length; [lia|done]|].
        iIntros "!>". iMod "Hclose". iModIntro.
        iCombine "Hctx Hp" as "H". iExact "H". }
      iApply (aneris_wp_lb_update with "Hlbl").
      wp_store.
      iIntros "#Hlbl' [Hctx Hp]".
      iMod (auth_list_extend _ _ v with "HTl HT_at") as "(HTl & HT_at & Hfrag)".
      iModIntro.
      iSplitL "HTl HTr HRl HRr Hctx".
      { iModIntro. iNext. iExists (Tl ++ [v]), Tr, Rl, Rr.
        rewrite app_length. simpl.
        replace (length Tl + 1) with (S (length Tl)) by lia.
        iFrame "#∗".
        rewrite list_minus_prefix_app; [|done]. iFrame.
        iSplit; [|done].
        iPureIntro. by apply prefix_app_r. }
      iModIntro.
      wp_smart_apply (monitor_signal_spec with "[Hlocked Hsbuf Hvs HsidLBLoc' Hsidx' Hfrag]").
      { iFrame "#∗". iExists rv, (vs ++ [(#(sidLB + length vs), v)%V]), sidLB.
        rewrite app_length /=.
        replace (Z.of_nat (length vs + 1)%nat) with (length vs + 1)%Z by lia.
        rewrite !Z.add_assoc !plus_assoc.
        iFrame. iSplit; [done|]. iSplit; [|done].
        iExists _. rewrite Nat.add_0_r. by eauto. }
      iIntros "(Hlocked & Hsbufdef)".
      wp_smart_apply (monitor_release_spec with "[$Hlocked Hsbufdef]").
      { iFrame "#∗". }
      iIntros (v'') "->".
      iApply "HΦ".
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _, _, _, _.
      iFrame. iSplit; [done|].
      simpl. rewrite Nat.add_1_r. iFrame "#∗"; eauto.
    - iApply (aneris_wp_lb_step with "Hlbl [Hctx Hp]"); [done| |].
      { iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
        iIntros "!>!>".
        iMod (iProto_send_r with "Hctx Hp []") as "[Hctx Hp]".
        { rewrite iMsg_base_eq /=; auto. }
        iApply step_fupdN_intro; [done|].
        iIntros "!>". iApply (bi.laterN_le (length (list_minus Tl Rr)));
          [rewrite list_minus_prefix_length; [lia|done]|].
        iIntros "!>". iMod "Hclose". iModIntro.
        iCombine "Hctx Hp" as "H". iExact "H". }
      iApply (aneris_wp_lb_update with "Hlbr").
      wp_store.
      iIntros "#Hlbr' [Hctx Hp]".
      iMod (auth_list_extend _ _ v with "HTr HT_at") as "(HTr & HT_at & Hfrag)".
      iModIntro.
      iSplitL "HTl HTr HRl HRr Hctx".
      { iModIntro. iNext. iExists Tl, (Tr ++ [v]), Rl, Rr.
        rewrite app_length /=.
        replace (length Tr + 1) with (S (length Tr)) by lia.
        iFrame "#∗".
        rewrite list_minus_prefix_app; [|done].
        iSplit; [done|]. iFrame.
        iPureIntro. by apply prefix_app_r. }
      iModIntro.
      wp_smart_apply (monitor_signal_spec with "[Hlocked Hsbuf Hvs HsidLBLoc' Hsidx' Hfrag]").
      { iFrame "#∗". iExists rv, (vs ++ [(#(sidLB + length vs), v)%V]), sidLB.
        rewrite app_length /=.
        replace (Z.of_nat (length vs + 1)%nat) with (length vs + 1)%Z by lia.
        rewrite !Z.add_assoc !plus_assoc.
        iFrame. iSplit; [done|]. iSplit; [|done].
        iExists _. rewrite Nat.add_0_r. by eauto. }
      iIntros "(Hlocked & Hsbufdef)".
      wp_smart_apply (monitor_release_spec with "[$Hlocked Hsbufdef]").
      { iFrame "#∗". }
      iIntros (v'') "->".
      iApply "HΦ".
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _, _, _, _.
      iFrame. iSplit; [done|].
      simpl. rewrite Nat.add_1_r. iFrame "#∗"; eauto.
  Qed.

  Lemma send_spec_tele_internal {TT} γe c (tt : TT) (v : TT → val) (P : TT → iProp Σ)
        (p : TT → iProto Σ) ip serA :
    {{{ c ↣{ γe, ip, serA } (<!.. (x : TT) > MSG (v x) {{ P x }}; p x)%proto ∗ P tt ∗
          ⌜Serializable serA (v tt)⌝ }}}
      send c (v tt) @[ip]
    {{{ RET #(); c ↣{ γe, ip, serA } (p tt)%proto }}}.
  Proof.
    iIntros (Φ) "(Hc & HP & Hser) HΦ".
    iDestruct (iProto_mapsto_le _ _ _ _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
      as "Hc".
    { iIntros "!>". iApply iProto_le_trans. iApply iProto_le_texist_intro_l.
      by iFrame "HP". }
    by iApply (send_spec_internal with "[$Hc $Hser]").
  Qed.

End Proof_of_send.

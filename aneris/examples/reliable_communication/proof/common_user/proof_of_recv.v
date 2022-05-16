From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import assert_proof lock_proof monitor_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From stdpp Require Import base tactics telescopes.
From aneris.examples.reliable_communication Require Import client_server_code.
From aneris.examples.reliable_communication.resources Require Import chan_endpoints_resources.

Section Proof_of_recv.
  Context `{!anerisG Mdl Σ,
            !chanG Σ,
            !lockG Σ,
            !server_ghost_names}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma try_recv_spec_internal {TT} γe (c : val) (v : TT → val) (P : TT → iProp Σ)
        (p : TT → iProto Σ) ip ser :
    {{{ c ↣{ γe, ip, ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto }}}
      try_recv c @[ip]
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ c ↣{ γe, ip, ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto) ∨
                   (∃ x : TT,  ⌜w = SOMEV (v x)⌝ ∗ c ↣{ γe, ip, ser } (p x)%proto ∗ P x) }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite iProto_mapsto_eq.
    iDestruct "Hc" as (γs s serl _serf sa dst) "Hc".
    iDestruct "Hc"
      as (sbuf slk rbuf rlk sidLBLoc ackIdLoc sidx ridx -> Heqc) "(%Heqg & Hc)".
    iDestruct "Hc"
      as "(Hl & %Hleq & HT_at & HR_at & Hsidx & Hridx
                 & #HsnT & #HaT & #HsT & #HidxsT
                 & Hp & #Hslk & #Hrlk & #Hinv)".
    wp_lam.
    wp_pures.
    wp_apply (acquire_spec with "Hrlk").
    iIntros (w) "[%Heq [Hlocked Hlk]]".
    wp_pures.
    iDestruct "Hlk" as (q vs ridx') "(Hrbuf & %Hq & HackIdLoc & Hridx' & Hvs)".
    wp_load.
    wp_apply (wp_queue_take_opt); [done|].
    iIntros (rv [[-> ->] | Hqeq]).
    { wp_pures.
      wp_apply (release_spec with "[$Hrlk $Hlocked Hrbuf HackIdLoc Hridx' Hvs]").
      { iExists _, _, _. by iFrame. }
      iIntros (w' ->). wp_pures. iApply "HΦ".
      iLeft. iSplitR; [done|].
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _, _, _, _.
      by iFrame "#∗"; eauto. } Unshelve.
    destruct Hqeq as (h & t & tv & -> & -> & Hq').
    iDestruct "Hvs" as "[(%w' & -> & Hfrag) Hvs]".
    wp_pures.
    wp_bind (Store _ _).
    iInv (chan_N (endpoint_chan_name γe)) as "IH".
    iDestruct "IH" as (Tl Tr Rl Rr) "(HTl & HTr & HRl & HRr & IH)".
    iDestruct "IH" as "(>%Hpre1 & >%Hpre2 & Hlbl & Hlbr & Hctx)".
    wp_store.
    iDestruct (mono_nat_auth_own_agree with "Hridx Hridx'") as %[_ <-].
    (* TODO: Fix weird split behaviour *)
    iMod (mono_nat_own_update (ridx + 1) with "[Hridx Hridx']")
      as "[Hridx _]";
      [|iApply fractional_half;
        [apply mono_nat_auth_own_as_fractional|iFrame]|]; [lia|].
    iDestruct "Hridx" as "[Hridx Hridx']".
    destruct s => /=.
    - iDestruct (auth_list_agree with "HTr Hfrag") as %Hnth.
      iDestruct (auth_list_length with "HRl HR_at") as %Hlen.
      rewrite -Hlen in Hnth.
      rewrite Nat.add_0_r in Hnth.
      rewrite (list_minus_alt Rl Tr); [|done].
      rewrite (drop_S _ w'); [|done].
      assert ((Rl ++ [w']) `prefix_of` Tr).
      { destruct Hpre2 as [xs ->].
        apply prefix_app.
        rewrite lookup_app_r in Hnth; [|lia].
        rewrite Nat.sub_diag in Hnth.
        rewrite -head_lookup in Hnth.
        destruct xs; [done|].
        simpl in Hnth.
        apply prefix_cons_alt; [|apply prefix_nil].
        by inversion Hnth. }
      iMod (iProto_recv_l with "Hctx Hp") as (p') "(Hctx & Hp &HP)".
      iMod (auth_list_extend _ _ w' with "HRl HR_at") as "(HRl & HR_at & _)".
      iModIntro.
      iSplitL "HTl HTr HRl HRr Hlbl Hlbr Hctx".
      { iNext.
        iExists Tl, Tr, (Rl ++ [w']), Rr.
        iFrame.
        iSplit; [done|].
        iSplit; [done|].
        replace (S (length Rl)) with (length (Rl ++ [w'])); last first.
        { rewrite app_length /=. lia. }
        by rewrite -(list_minus_alt (Rl ++ [w']) Tr). }
      wp_pures.
      wp_apply (release_spec with "[$Hrlk $Hlocked Hrbuf HackIdLoc Hvs Hridx']").
      { iExists _, _, _. iFrame. iSplit; [done|]. simpl.
        rewrite !Nat.add_1_r.
        rewrite -!Nat2Z.inj_add.
        rewrite -Nat.add_succ_comm.
        iFrame.
        iApply (big_sepL_impl with "Hvs").
        iIntros "!>" (k x Hlookup) "Hv".
        rewrite Nat.add_succ_comm.
        rewrite -!Nat2Z.inj_add.
        rewrite -Nat.add_succ_comm.
        done. }
      iIntros (w'' ->).
      iPoseProof (iMsg_texist_exist with "HP") as (x) "HP".
      rewrite iMsg_base_eq /=.
      wp_pures.
      iApply "HΦ".
      iRight.
      iDestruct "HP" as "(%Heq'' & Hp' & HP)".
      rewrite -Heq''.
      iExists _. iSplit; [done|].
      iFrame.
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _, _, _, _.
      iSplit; [done|].
      iRewrite "Hp'".
      iFrame "#∗".
      rewrite Nat.add_1_r.
      eauto.
    - iDestruct (auth_list_agree with "HTl Hfrag") as %Hnth.
      iDestruct (auth_list_length with "HRr HR_at") as %Hlen.
      rewrite -Hlen in Hnth.
      rewrite Nat.add_0_r in Hnth.
      rewrite (list_minus_alt Rr Tl); [|done].
      rewrite (drop_S _ w'); [|done].
      assert ((Rr ++ [w']) `prefix_of` Tl).
      { destruct Hpre1 as [xs ->].
        apply prefix_app.
        rewrite lookup_app_r in Hnth; [|lia].
        rewrite Nat.sub_diag in Hnth.
        rewrite -head_lookup in Hnth.
        destruct xs; [done|].
        simpl in Hnth.
        apply prefix_cons_alt; [|apply prefix_nil].
        by inversion Hnth. }
      iMod (iProto_recv_r with "Hctx Hp") as (p') "(Hctx & Hp &HP)".
      iMod (auth_list_extend _ _ w' with "HRr HR_at") as "(HRr & HR_at & _)".
      iModIntro.
      iSplitL "HTl HTr HRl HRr Hlbl Hlbr Hctx".
      { iNext.
        iExists Tl, Tr, Rl, (Rr ++ [w']).
        iFrame.
        iSplit; [done|].
        iSplit; [done|].
        replace (S (length Rr)) with (length (Rr ++ [w'])); last first.
        { rewrite app_length /=. lia. }
        by rewrite -(list_minus_alt (Rr ++ [w']) Tl). }
      wp_pures.
      wp_apply (release_spec with "[$Hrlk $Hlocked Hrbuf HackIdLoc Hvs Hridx']").
      { iExists _, _, _. iFrame. iSplit; [done|]. simpl.
        rewrite !Nat.add_1_r.
        rewrite -!Nat2Z.inj_add.
        rewrite -Nat.add_succ_comm.
        iFrame.
        iApply (big_sepL_impl with "Hvs").
        iIntros "!>" (k x Hlookup) "Hv".
        rewrite Nat.add_succ_comm.
        rewrite -!Nat2Z.inj_add.
        rewrite -Nat.add_succ_comm.
        done. }
      iIntros (w'' ->).
      iPoseProof (iMsg_texist_exist with "HP") as (x) "HP".
      rewrite iMsg_base_eq /=.
      wp_pures.
      iApply "HΦ".
      iRight.
      iDestruct "HP" as "(%Heq'' & Hp' & HP)".
      rewrite -Heq''.
      iExists _. iSplit; [done|].
      iFrame.
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _, _, _, _.
      iSplit; [done|].
      iRewrite "Hp'".
      iFrame "#∗".
      rewrite Nat.add_1_r.
      eauto.
  Qed.

  Lemma recv_spec_internal {TT} γe c (v : TT → val) (P : TT → iProp Σ)
             (p : TT → iProto Σ) ip ser :
    {{{ c ↣{ γe, ip, ser } (<?.. x> MSG (v x) {{ ▷ P x }}; p x)%proto }}}
      recv c @[ip]
    {{{ x, RET v x; c ↣{ γe, ip, ser } p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_lam.
    wp_pures.
    iLöb as "IH".
    wp_apply (try_recv_spec_internal with "Hc").
    iIntros (w) "[[%Heq Hc] | H]".
    { rewrite Heq. wp_pures. by iApply ("IH" with "Hc"). }
    iDestruct "H" as (tt ->) "[Hc HP]".
    wp_pures. iApply "HΦ". by iFrame.
  Qed.

End Proof_of_recv.

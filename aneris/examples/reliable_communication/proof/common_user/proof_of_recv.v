From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import assert_proof lock_proof monitor_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting step_update.
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

  Lemma try_recv_spec_internal {TT} (c : val) (v : TT → val) (P : TT → iProp Σ)
        (p : TT → iProto Σ) ip ser :
    {{{ c ↣{ ip, ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto }}}
      try_recv c @[ip]
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ c ↣{ ip, ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto) ∨
                   (∃ x : TT,  ⌜w = SOMEV (v x)⌝ ∗ c ↣{ ip, ser } (p x)%proto ∗ P x) }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite iProto_mapsto_eq.
    iDestruct "Hc" as (s sbuf slk rbuf rlk sidLBLoc ackIdLoc sidx ridx γe) "Hc".
    iDestruct "Hc" as (->) "(Hsidx & Hridx & Hp & #Hslk & #Hrlk)".
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
      iExists _, _, _, _, _, _, _, _. iExists _, _.
      iFrame. iFrame "#". eauto. }
    destruct Hqeq as (h & t & tv & -> & -> & Hq').
    iDestruct "Hvs" as "[Hfrag Hvs]".
    wp_pures.
    wp_bind (Store _ _).
    iDestruct (mono_nat_auth_own_agree with "Hridx Hridx'") as %[_ <-].
    (* TODO: Fix weird split behaviour *)
    iMod (mono_nat_own_update (ridx + 1) with "[Hridx Hridx']")
      as "[Hridx _]";
      [|iApply fractional_half;
        [apply mono_nat_auth_own_as_fractional|iFrame]|]; [lia|].
    iDestruct "Hridx" as "[Hridx Hridx']".
    replace (ridx + 0) with ridx by lia.
    iApply (aneris_wp_step_update _ _ ∅ with "[Hp Hfrag]");
      [done|by iApply (step_update_recv with "Hp Hfrag")|].
    wp_store.
    iDestruct 1 as (p') "[Hp HP]".
    iModIntro.
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
    iExists _, _, _, _, _, _, _, _. iExists _, _.
    iSplit; [done|].
    rewrite Nat.add_1_r.
    iFrame=> /=.
    iRewrite "Hp'".
    iFrame. by iFrame "#".
  Qed.

  Lemma recv_spec_internal {TT} c (v : TT → val) (P : TT → iProp Σ)
             (p : TT → iProto Σ) ip ser :
    {{{ c ↣{ ip, ser } (<?.. x> MSG (v x) {{ ▷ P x }}; p x)%proto }}}
      recv c @[ip]
    {{{ x, RET v x; c ↣{ ip, ser } p x ∗ P x }}}.
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

From iris.algebra Require Import agree auth excl gmap dfrac max_prefix_list.
From iris.algebra Require Import updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof assert_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Export log_code.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import log_resources.

Import lock_proof.

Section Log.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context {Aty : Type}.
  Notation A := (leibnizO Aty).
  Context `{inG Σ (mono_listUR A)}.
  Context `[!Inject A val].

  Lemma wp_log_create ip :
    {{{ True }}}
      log_create #() @[ip]
    {{{ logL logV, RET #logL; logL ↦[ip] logV ∗ ⌜is_log [] logV⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    wp_alloc l as "Hl".
    iApply "HΦ". iFrame. iPureIntro.
    by eexists.
    Qed.

  Lemma wp_log_add_entry ip logL logV logM (x : A) :
    {{{ ⌜is_log logM logV⌝ ∗ logL ↦[ip] logV }}}
      log_add_entry #logL $x @[ip]
    {{{ logV', RET #();
        ⌜is_log (logM ++ [x]) logV'⌝ ∗ logL ↦[ip] logV' }}}.
  Proof.
    iIntros (Φ) "(%Hl & Hp) HΦ".
    destruct Hl as (lV & -> & Hlst).
    wp_lam. wp_pures.
    wp_load. wp_pures.
    wp_apply (wp_list_cons _ []); first done.
    iIntros (v) "%Hl2".
    wp_apply wp_list_append; first done.
    iIntros (v') "%Hl'".
    wp_pures.
    wp_store.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    eexists; rewrite app_length /=; split; last done.
    do 3 f_equal; lia.
  Qed.


  Lemma wp_log_next ip logL logV logM q :
    {{{ ⌜is_log logM logV⌝ ∗ logL ↦[ip]{q} logV }}}
      log_next #logL @[ip]
    {{{ n, RET #n;
        ⌜n = List.length logM⌝ ∗ ⌜is_log (logM) logV⌝ ∗ logL ↦[ip]{q} logV}}}.
  Proof.
    iIntros (Φ) "(%Hl & Hp) HΦ".
    destruct Hl as (lV & -> & Hlst).
    wp_lam.
    wp_load.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; by eexists.
  Qed.

  Lemma wp_log_length ip logL logV logM q :
    {{{ ⌜is_log logM logV⌝ ∗ logL ↦[ip]{q} logV }}}
      log_length #logL @[ip]
    {{{ n, RET #n;
        ⌜n = List.length logM⌝ ∗ ⌜is_log (logM) logV⌝ ∗ logL ↦[ip]{q} logV}}}.
  Proof.
    iIntros (Φ) "(%Hl & Hp) HΦ".
    destruct Hl as (lV & -> & Hlst).
    wp_lam.
    wp_load.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; by eexists.
  Qed.

Lemma wp_log_get ip logL logV logM i q :
    {{{ ⌜i < List.length logM⌝ ∗
        ⌜is_log logM logV⌝ ∗ logL ↦[ip]{q} logV }}}
      log_get #logL #i @[ip]
    {{{ x, RET (SOMEV $x);
        ⌜List.nth_error logM i = Some x⌝ ∗
        ⌜is_log (logM) logV⌝ ∗ logL ↦[ip]{q} logV}}}.
  Proof.
    iIntros (Φ) "(%Hi & %Hl & Hp) HΦ".
    destruct Hl as (lV & -> & Hlst).
    wp_lam.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_list_nth_some; [eauto with lia|].
    iIntros (v (x & -> & Hsome)).
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; eauto; last by eexists.
  Qed.

  Lemma wp_log_wait_until ip
    γlog q logM (* created at the logical setup *)
    monγ monV monR logL logV i (* created at the allocation of physical data *):
    {{{ ⌜i ≤ List.length logM⌝ ∗ ⌜is_log logM logV⌝ ∗
        is_monitor ip monγ monV (log_monitor_inv_def ip γlog q logL monR) ∗
        locked monγ ∗ (monR logM) ∗ logL ↦[ip] logV ∗ own_log_auth γlog q logM }}}
      log_wait_until #logL monV #i @[ip]
    {{{ logV' logM', RET #();
        ⌜i < List.length logM'⌝ ∗ ⌜is_log logM' logV'⌝ ∗
        locked monγ ∗ (monR logM') ∗ logL ↦[ip] logV' ∗ own_log_auth γlog q logM' }}}.
  Proof.
    iIntros (Φ) "(%Hi & %Hl & #Hmon & Hlocked & Hres & Hp & Hown) HΦ".
    wp_lam.
    wp_pures.
    case_bool_decide as Hi2 ; first by lia.
    wp_pures.
    wp_apply (wp_log_next with "[$Hp //]").
    iIntros (n) "(-> & _ & Hp)".
    wp_pures.
    case_bool_decide as Hiz; first by lia.
    wp_pure _.
    clear Hiz Hi2.
    iDestruct (get_obs with "Hown") as "#Hobs".
    iLöb as "IH" forall (logV logM Hl Hi) "Hres Hp Hown Hobs".
    wp_pures.
    wp_apply (wp_log_next with "[$Hp //]").
    iIntros (n) "(-> & _ & Hp)".
    wp_pures.
    case_bool_decide as Hiz2.
    - wp_pure _.
      wp_apply (monitor_wait_spec with "[$Hmon Hres $Hlocked Hp Hown]").
      iExists _, _. iFrame. eauto.
      iIntros (v) "(-> & Hlocked & Hres)".
      iDestruct "Hres" as (logV' logM' Hlog') "(Hp & Hown & Hres)".
      do 2 wp_pure _.
      iDestruct (own_obs_prefix with "[$Hown][$Hobs]") as "%Hpre".
      assert (i ≤ length logM') as Hi'.
      list_simplifier.
      by apply prefix_length.
      iSpecialize ("IH" $! logV' logM' Hlog' Hi').
      iDestruct (get_obs with "Hown") as "#Hobs'".
      iApply ("IH" with "[$Hlocked][$HΦ][$Hres][$Hp][$Hown][$Hobs']").
    - wp_pure _.
      wp_apply wp_assert.
       wp_pures.
      iSplitR.
      iPureIntro.
      f_equal.
      case_bool_decide; eauto with lia.
      iNext.
      iApply "HΦ".
      iFrame.
      eauto with lia.
  Qed.

  End Log.

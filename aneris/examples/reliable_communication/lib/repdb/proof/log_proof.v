From iris.algebra Require Import agree auth excl gmap dfrac.
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
     Require Import ras resources_def.

Import lock_proof.


  (* ------------------------------------------------------------------------ *)
  Section Log.
    Context `{!anerisG Mdl Σ, !lockG Σ}.
  Definition inject_log `{!Inject A val} (xs : list A) :=
    ($xs, #(List.length xs))%V.

  Global Program Instance Inject_log `{!Inject A val}
    : Inject (list A) val := {| inject := inject_log |}.
  Next Obligation.
    intros ? [] xs ys. inversion 1 as [[Hinj Hinj2]].
    by apply Inject_list in Hinj.
  Qed.

  Context `[!Inject A val].

  Definition is_log (logM : list A) (logV : val) :=
    ∃ (lV : val), logV = (lV, #(List.length logM))%V ∧ is_list logM lV.

  Lemma is_log_inject xs l :
    is_log xs l ↔ l = $xs.
  Proof. Admitted.

  (* Definition is_logLoc (logM : list A) (logL : loc) : iProp Σ := *)
  (*   ∃ (logV : val), logL ↦[ip] logV ∗ ⌜is_log logM logV⌝. *)

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


  (* Definition logMonitor_res *)
  (*  ip (γlog : gname) (logL : loc) (Res : list A → iProp Σ) : iProp Σ := *)
  (* ∃ logV logM, *)
  (*   ⌜is_log logM logV⌝ ∗ *)
  (*   logL ↦[ip] logV ∗ *)
  (*   own_log_local γlog logM ∗ *)
  (*   Res logM. *)

(*
  Lemma wp_log_wait_until ip monN monγ monV monR logL logV logM i :
    {{{ ⌜i ≤ List.length logM⌝ ∗
        ⌜is_log logM logV⌝ ∗
        is_monitor monN ip monγ monV (logMonitor_res ip logL monR) ∗
        lock_proof.locked monγ ∗ (monR logM) ∗
        logL ↦[ip] logV }}}
      log_wait_until #logL monV #i @[ip]
    {{{ logV' logM', RET #();
        ⌜i < List.length logM'⌝ ∗
        ⌜is_log logM' logV'⌝ ∗
        lock_proof.locked monγ ∗ (monR logM') ∗
        logL ↦[ip] logV' }}}.
  Proof.
    iIntros (Φ) "(%Hi & %Hl & #Hmon & Hlocked & Hres & Hp) HΦ".
    assert (is_log logM logV) as Hlc by done.
    destruct Hlc as (lV & -> & Hlst).
    wp_lam.
    wp_pures.
    case_bool_decide; first by lia.
    wp_pures.
    wp_apply (wp_log_next with "[$Hp //]").
    iIntros (n) "(-> & %Hlc & Hp)".
    wp_pures.
    case_bool_decide as Hiz; first by lia.
    wp_pure _.
    clear Hlc.
    iLöb as "IH" forall (logM lV Hi Hl Hlst Hiz) "Hres".
    wp_pures.
    wp_apply (wp_log_next with "[$Hp //]").
    iIntros (n) "(-> & _ & Hp)".
    wp_pures.
    case_bool_decide as Hiz2.
    - wp_pure _.
      wp_apply (monitor_wait_spec with "[$Hmon Hres $Hlocked Hp]").
      iExists _, _. iFrame. eauto.
      iIntros (v) "(-> & Hlocked & Hres)".
      iDestruct "Hres" as (logV' logM' Hlog') "(Hp & Hres)".
      do 2 wp_pure _.
      clear Hi Hl Hlst Hiz Hiz2 logM.
      iSpecialize ("IH" $! logM' logV').
      iApply ("IH" with "[][][][][$Hlocked][][][$Hres]").

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
    (* -------- *)
    iLöb as "IH".
    wp_pures.
    wp_apply (wp_log_next with "[$Hp //]").
    iIntros (n) "(-> & _ & Hp)".
    wp_pures.
    case_bool_decide as Hiz2.
    - wp_pure _.
      wp_apply (monitor_wait_spec with "[$Hmon Hres $Hlocked Hp]").
      iExists _, _. iFrame. eauto.
      iIntros (v) "(-> & Hlocked & Hres)".
      iDestruct "Hres" as (logV' logM' Hlog') "(Hp & Hres)".
      do 2 wp_pure _.
      iApply ("IH" with "[$Hlocked][Hres]").
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


log_wait_until =
(λ: "log" "mon" "i",
   letrec: "aux" <> :=
     let: "n" := log_next "log" in
     if: "n" = "i" then monitor_wait "mon" ;; "aux" #()
     else assert: "i" < "n" in
   if: if: "i" < #0 then #true else log_next "log" < "i" then assert: #false
   else "aux" #())%V
     : val


     Definition log_wait_until : val.

*)
  End Log.

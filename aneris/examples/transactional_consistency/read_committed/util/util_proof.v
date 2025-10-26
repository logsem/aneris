From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import user_params aux_defs.
From aneris.examples.transactional_consistency Require Import code_api.
From aneris.examples.transactional_consistency Require Import resource_algebras.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From iris.algebra Require Import gmap.
From iris.algebra Require Import excl.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_code.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation.

Section proof.

  Context `{!anerisG Mdl Σ, !User_params, !RC_resources Mdl Σ}.

  Lemma wait_transaction_spec :
    ∀ (c cond v : val) (key : Key) (sa : socket_address) (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜key ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗
    GlobalInv -∗
    RC_client_toolbox -∗
    □ (|={⊤, E}=> ▷ ∃ V, key ↦ₖ V ∗ (key ↦ₖ V ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}}
            cond v' @[ip_of_address sa]
           {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{ ConnectionState c sa CanStart }}}
        weak_wait_transaction c cond #key @[ip_of_address sa]
    {{{ V, RET #(); ConnectionState c sa CanStart ∗ Seen key ({[v]} ∪ V) }}}.
  Proof.
    iIntros (c cond v key sa E) "%Hsub %Hin #Hginv #Hconn (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #Hshift #Htest !# %Φ Hstate HΦ".
    rewrite /weak_wait_transaction.
    wp_pures.
    wp_apply ("Hst" with "[$]"); first done.
    iPoseProof "Hshift" as "Hshift'".
    iMod "Hshift'"; do 2 iModIntro;
      iDestruct "Hshift'" as "[%V (Hkey & Hclose)]".
    iExists {[ key := V ]}.
    rewrite big_sepM_singleton.
    iFrame.
    iIntros "(Hstate & Hkey & Hkey_con)".
    rewrite big_sepM_singleton.
    iMod ("Hclose" with "[$Hkey]") as "_".
    iModIntro.
    wp_pures.
    iLöb as "IH".
    wp_apply ("Hrd" with "[//][$]"); first done.
    iPoseProof "Hshift" as "Hshift'".
    iMod "Hshift'"; do 2 iModIntro;
      iDestruct "Hshift'" as "[%V' (Hkey' & Hclose)]".
    iExists None, V'.
    iFrame.
    iIntros (wo) "(Hkey_con & Hkey & Hdisj)".
    iMod (Seen_creation with "[$][$Hkey]") as "(Hkey & Hseen)"; first done.
    iMod ("Hclose" with "[$Hkey]") as "_".
    iModIntro.
    iDestruct "Hdisj" as "[(_ & [[%v' (-> & %Hin')] | ->]) | (%Hfalse & _)]"; last done.
    - wp_pures.
      wp_apply ("Htest" with "[//]").
      iIntros (b) "%Hbeq".
      destruct b eqn:Heq_b; wp_pures.
      + rewrite /commitU.
        wp_pures.
        wp_apply ("Hcom" with "[$]"); first done.
        iMod "Hshift"; do 2 iModIntro;
          iDestruct "Hshift" as "[%V'' (Hkey & Hclose)]".
        iExists (dom {[key := V]}), {[key := None]}, {[key := V'']}.
        iFrame.
        iSplitR "Hclose HΦ Hseen".
        * do 2 rewrite big_sepM_singleton.
          iFrame.
          iSplitL.
          all : iPureIntro.
          all : set_solver.
        * iIntros (b') "(Hstate & Hkey)".
          rewrite big_sepM2_singleton; simpl.
          rewrite big_sepM_singleton.
          iDestruct "Hkey" as "[(_ & Hkey) | (_ & Hkey)]".
          all : iMod ("Hclose" with "[$Hkey]") as "_".
          all : iModIntro.
          all : wp_pures.
          all : iApply ("HΦ" $! (V' ∖ {[v]})).
          all : iFrame.
          all : assert (V' = {[v]} ∪ (V' ∖ {[v]})) as <-; last iFrame.
          all : assert (v = v') as ->; first by apply Hbeq.
          all : rewrite -union_difference_singleton_L; done.
      + iApply ("IH" with "[$][$][$]").
    - wp_pures.
      iApply ("IH" with "[$][$][$]").
  Qed.

End proof.

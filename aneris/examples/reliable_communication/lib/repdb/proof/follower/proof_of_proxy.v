From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras
     resources_def
     resources_global_inv
     resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     repdb_serialization.
From aneris.examples.reliable_communication.lib.repdb.proof.follower
     Require Import
     clients_at_follower_mt_user_params
     proof_of_clients_handler.

Section Client_Proxy_Proof.
  Context `{!anerisG Mdl Σ, dbparams : !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname).
  Context (fsa : socket_address).
  Context (Hin : fsa ∈ DB_followers).
  Context (follower_si : message → iProp Σ).
  Notation MTC := (client_handler_at_follower_user_params γL γM N fsa).

  Definition read_at_follower_spec_internal
           (rd : val) (csa fsaddr : socket_address) (k : Key) (h : wrlog) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ own_obs γL fsaddr h }}}
      rd #k @[ip_of_address csa]
    {{{vo, RET vo;
          ∃ h', ⌜h ≤ₚ h'⌝ ∗ own_obs γL fsaddr h' ∗
         ((⌜vo = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜at_key k h' = Some a⌝))
    }}}%I.

   Definition init_client_proxy_follower_spec_internal : iProp Σ :=
     ∀ A csa,
     ⌜fsa ≠ DB_addr⌝ →
     ⌜fsa ∈ A⌝ →
     ⌜csa ∉ A⌝ →
     {{{ fixed A ∗
         fsa ⤇ follower_si ∗
         csa ⤳ (∅, ∅) ∗
         (@init_client_proxy_spec _ _ _ _ MTC follower_si) ∗
         free_ports (ip_of_address csa) {[port_of_address csa]} }}}
       init_client_follower_proxy (s_serializer DB_serialization)
         #csa #fsa @[ip_of_address csa]
     {{{ rd, RET rd;
         (∀ k h, read_at_follower_spec_internal rd csa fsa k h) }}}.

  Lemma init_client_proxy_follower_internal_holds :
    Global_Inv γL γM N ⊢ init_client_proxy_follower_spec_internal.
  Proof.
    iIntros "#Hinv".
    iIntros (A csa).
    iIntros (Hneq HA HnA).
    iIntros (Φ) "!#".
    iIntros "(#Hf & #Hsi & Hmh & #HClient_proxySpec & Hfp) HΦ".
    rewrite /init_client_follower_proxy.
    wp_pures.
    wp_apply ("HClient_proxySpec" with "[$Hf $Hfp $Hmh $Hsi][HΦ]"); first done.
    iNext.
    iIntros (reqh) "#Hspec".
    iApply "HΦ".
    iIntros (k h).
    rewrite /read_at_follower_spec_internal.
    iIntros (Hkeys Ψ) "!#".
    iIntros "#Hobs HΨ".
    wp_apply ("Hspec" $! _ (k, h) with "[Hobs]").
    - iSplit.
      -- iPureIntro. apply _.
      -- iDestruct "Hobs" as "[(%Habs & _)|Hobs]".
         { naive_solver. }
         iDestruct "Hobs" as (γF') "(#Hknw & #HobsL & #HobsF)".
         iFrame "#".
         iExists k, h.
         iFrame "#∗".
         do 3 (iSplit; first done).
         iExists _; iFrame "#".
    - iIntros (repd repv) "Hpost".
      iApply "HΨ".
      simplify_eq /=.
      rewrite /ReqPost.
      iDestruct "Hpost"
        as (k' h0 h1) "(%Heq1 & -> & %Hpre & #Hreplog & #Hpost)".
      iExists h1.
      inversion Heq1; subst.
      iSplit; first done.
      iSplit.
      { iFrame "#". }
      iDestruct "Hpost" as "[%Hpost|Hpost]".
      -- iLeft. naive_solver.
      -- iRight. naive_solver.
  Qed.

End Client_Proxy_Proof.

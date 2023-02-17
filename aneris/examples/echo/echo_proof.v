From iris.algebra Require Import excl_auth.
From trillium.prelude Require Import finitary.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang.lib Require Import network_util_proof assert_proof.
From aneris.aneris_lang.lib Require Import list_code list_proof.
From aneris.examples.echo Require Export echo_code.
Set Default Proof Using "Type".

Class stringG Σ := { string_inG :> inG Σ (excl_authUR (leibnizO string)) }.
Definition stringΣ : gFunctors := #[GFunctor (excl_authUR (leibnizO string))].
Instance subG_stringΣ {Σ} : subG stringΣ Σ → stringG Σ.
Proof. solve_inG. Qed.

Section echo_server_proof.
  Context `{dG : !anerisG Mdl Σ}.

  Definition srv_si : message → iProp Σ :=
    λ m, (∃ Ψ P, P m ∗ m.(m_sender) ⤇ Ψ ∗
                 (∀ m', ⌜m.(m_body) = m'.(m_body)⌝ ∗ P m -∗ Ψ m'))%I.

  Lemma echo_server_spec (sa : socket_address) :
    {{{ free_ports (ip_of_address sa) {[(port_of_address sa)]} ∗
        sa ⤳ (∅, ∅) ∗ sa ⤇ srv_si }}}
      echo_server #sa @[ip_of_address sa]
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(Hfree & Hsa & #Hsi) HΦ".
    wp_lam.
    wp_socket sh as "Hsh".
    wp_pures.
    wp_socketbind.
    wp_pure _.
    (* TODO: This can be wrapped in a nice generalisation *)
    iAssert (∃ R T, sa ⤳ (R, T) ∗ ([∗ set] m ∈ R, ∃ Ψ, m.(m_sender) ⤇ Ψ) ∗
            ⌜∀ m, m ∈ R → ∃ m', m' ∈ T ∧
                                m.(m_body) = m'.(m_body) ∧
                                m'.(m_sender) = m.(m_destination) ∧
                                m'.(m_destination) = m.(m_sender)⌝)%I with
      "[Hsa]" as (R T) "(Hsa & HR & %HRT)"; [by eauto|].
    iRevert (HRT).
    iLöb as "IH" forall (R T).
    iIntros (HRT).
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hsa $Hsh $Hsi]"); try auto.
    iIntros (m) "(%Hdst & [H | H])".
    - iDestruct "H" as "(%Hnin & Hsh & Hsa & _ & Hm)".
      iDestruct "Hm" as (Ψ P) "(HP & #Hsi_clt & HΨ)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      wp_apply (aneris_wp_send with "[$Hsa $Hsh $Hsi_clt HP HΨ]");
        [try eauto..| |].
      { by iApply ("HΨ" with "[$HP]"). }
      iIntros "[Hsh Hsa]".
      do 2 wp_pure _.
      iApply ("IH" with "HΦ Hsh Hsa [HR]").
      { iApply big_sepS_union; [set_solver|]. iFrame "HR".
        rewrite big_sepS_singleton. by eauto. }
      iPureIntro.
      intros m' Hmin.
      apply elem_of_union in Hmin.
      destruct Hmin as [Hmin | Hmin].
      { assert (m' = m) as -> by set_solver.
        exists {|
          m_sender := sa;
          m_destination := m_sender m;
          m_body := m_body m
        |}. set_solver. }
      set_solver.
    - iDestruct "H" as "(%Hin & Hsh & Hsa)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      iDestruct (big_sepS_elem_of with "HR") as (Ψ) "#Hsi_clt"; [done|].
      wp_apply (aneris_wp_send_duplicate with "[$Hsa $Hsh $Hsi_clt]"); try auto.
      { destruct (HRT _ Hin) as [m' (Hmin' & Hbody' & Hsrc' & Hdst')].
        destruct m'. simplify_eq. simpl in *. simplify_eq. done. }
      iIntros "[Hsh Hsa]".
      do 2 wp_pure _.
      by iApply ("IH" with "HΦ Hsh Hsa HR").
  Qed.

End echo_server_proof.

Section echo_client_proof.
  Context `{dG : !anerisG Mdl Σ}.
  Context `{strG : !stringG Σ}.

  Definition own_auth (γ : gname) (mb : message_body) : iProp Σ :=
    own γ (●E (mb:leibnizO string)).
  Definition own_frag (γ : gname) (mb : message_body) : iProp Σ :=
    own γ (◯E (mb:leibnizO string)).

  Definition clt_si γ : message → iProp Σ :=
    λ m, own_frag γ (m.(m_body)).

  Lemma echo_client_spec (sa srv_sa : socket_address) :
    {{{ unallocated {[sa]} ∗
        free_ports (ip_of_address sa) {[(port_of_address sa)]} ∗
        sa ⤳ (∅, ∅) ∗ srv_sa ⤇ srv_si }}}
      echo_client #sa #srv_sa @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof using Mdl dG strG Σ.
    iIntros (Φ) "(Hunallocated & Hfree & Hsa & #Hsrv_si) HΦ".
    wp_lam.
    wp_pures.
    wp_socket sh as "Hsh".
    iMod (own_alloc (●E("Hello":leibnizO string) ⋅
                     ◯E("Hello":leibnizO string))) as (γ) "[Hauth Hfrag]".
    { apply excl_auth_valid. }
    iApply (aneris_wp_socket_interp_alloc_singleton (clt_si γ)
             with "Hunallocated").
    iIntros "#Hsi".
    wp_pures.
    wp_socketbind.
    wp_apply (aneris_wp_send with "[$Hsh $Hsa Hsrv_si Hfrag]"); [try done..|].
    { iFrame "#".
      iExists (clt_si γ), (λ m, (own_frag γ m.(m_body))).
      iFrame "#∗". iIntros "!>" (m) "[%Hm Hm]". by rewrite Hm. }
    iIntros "[Hsh Hsa]".
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hsh $Hsa $Hsi]"); [try done..|].
    iIntros (m) "[%Hdst [H|H]]"; last first.
    { iDestruct "H" as "[%Hin _]"; set_solver. }
    iDestruct "H" as "(%Hnin & Hsh & Hsa & _ & Hfrag)".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hhello%excl_auth_agree_L.
    iMod (own_update_2 with "Hauth Hfrag") as "[Hauth Hfrag]".
    { apply (excl_auth_update _ _ ("World":leibnizO string)). }
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    wp_apply (aneris_wp_send with "[$Hsh $Hsa Hsrv_si Hfrag]"); [try done..|].
    { iFrame "#".
      iExists (clt_si γ), (λ m, (own_frag γ m.(m_body))).
      iFrame "#∗". simpl. iIntros "!>" (m') "[%Hm Hm]". by rewrite Hm. }
    iIntros "[Hsh Hsa]".
    wp_pures.
    wp_apply (wp_list_cons ((m_body m), (m_sender m)) []).
    { iPureIntro. done. }
    iIntros (v Hl).
    wp_apply (wp_wait_receivefresh with "[$Hsh $Hsa $Hsi]"); [done| |].
    { simpl.
      rewrite !union_empty_r_L gset_map_singleton.
      by rewrite -Hdst pair_to_msg_id. }
    iIntros (m') "[%Hdst' H]".
    iDestruct "H" as "(Hsh & Hsa & Hfrag)".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hworld%excl_auth_agree_L.
    do 8 wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    iSplit; [iPureIntro; rewrite Hhello; case_bool_decide; done|].
    iIntros "!>".
    do 2 wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    iSplit; [iPureIntro; rewrite Hworld; case_bool_decide; done|].
    by iApply "HΦ".
  Qed.

End echo_client_proof.

Definition echo_is :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
  |}.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_addr := SocketAddressInet "0.0.0.1" 80.

Definition ips : gset string :=
  {[ ip_of_address server_addr ; ip_of_address client_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_addr ]}.

Theorem echo_safe :
  aneris_adequate echo_runner "system" echo_is (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; stringΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅); try set_solver.
  { apply unit_model_rel_finitary. }
  iIntros (dinvG).
  iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
  iDestruct (unallocated_split with "Hunallocated") as "[Hsrv Hclt]";
    [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton srv_si with "Hsrv").
  iIntros "#Hsrv_si".
  rewrite big_sepS_union; [|set_solver].
  rewrite !big_sepS_singleton.
  iDestruct "Hhist" as "[Hhist_srv Hhist_clt]".
  rewrite big_sepS_union; [|set_solver].
  rewrite !big_sepS_singleton.
  iDestruct "Hips" as "[Hip_srv Hip_clt]".
  rewrite /echo_runner.
  wp_pures.
  wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
  iSplitL "Hip_srv"; [done|].
  iSplitR "Hhist_srv"; last first.
  { iIntros "!> Hfree".
    replace ("0.0.0.0") with (ip_of_address (SocketAddressInet "0.0.0.0" 80))
      by eauto.
    iApply (echo_server_spec with "[Hfree $Hhist_srv $Hsrv_si]"); [|done].
    iFrame. }
  iIntros "!>". wp_pures.
  wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
  iSplitL "Hip_clt"; [done|].
  iSplitR "Hhist_clt Hclt"; [done|].
  iIntros "!> Hfree".
  replace ("0.0.0.1") with (ip_of_address (SocketAddressInet "0.0.0.1" 80))
                           by eauto.
  iApply (echo_client_spec with "[Hfree $Hhist_clt $Hclt $Hsrv_si]"); [|done].
  iFrame.
Qed.

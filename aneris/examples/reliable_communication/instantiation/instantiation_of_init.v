From aneris.algebra Require Import monotone.
From iris.algebra Require Import gmap agree auth numbers excl frac_auth gset csum.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import coq_tactics reduction spec_patterns tactics.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import inject lock_proof list_proof pers_socket_proto.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.spec Require Import ras resources api_spec.
From aneris.examples.reliable_communication.resources Require Import prelude.
From aneris.examples.reliable_communication.instantiation Require Import
     instantiation_of_resources
     instantiation_of_client_specs
     instantiation_of_server_specs
     instantiation_of_send_and_recv_specs.

Section Init_initialisation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!SpecChanG Σ}.

  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma Reliable_communication_init_instance
        E (UP : Reliable_communication_service_params) :
    ↑RCParams_srv_N ⊆ E →
    True ⊢ |={E}=>
        ∃ ( _ : Chan_mapsto_resource),
        ∃ ( _ : server_ghost_names),
        ∃ (SnRes : SessionResources UP),
          SrvInit ∗
          ⌜(∀ sa A, make_client_skt_spec UP SnRes sa A)⌝ ∗
          ⌜(∀ A, make_server_skt_spec UP SnRes A)⌝ ∗
          ⌜(∀ skt sa, connect_spec UP SnRes skt sa)⌝ ∗
          ⌜(∀ skt, server_listen_spec UP SnRes skt)⌝ ∗
          ⌜(∀ skt, accept_spec UP SnRes skt)⌝ ∗
          ⌜(∀ c v p ip ser, send_spec c v p ip ser)⌝ ∗
          ⌜(∀ TT c t v P q ip s, send_spec_tele TT c t v P q ip s)⌝ ∗
          ⌜(∀ TT c v P q ip ser, try_recv_spec TT c v P q ip ser)⌝ ∗
          ⌜(∀ TT c v P q ip ser, recv_spec TT c v P q ip ser)⌝.
  Proof.
    iIntros (Hne _).
    iMod (own_alloc (● ((to_agree <$> ∅) : session_names_mapUR)))
      as (γ_srv_kn_s_name) "Hkns"; first by apply auth_auth_valid.
    iMod (own_alloc (● (∅ : gsetUR message) ⋅ (◯ (∅ : gsetUR message))))
      as (γ_srv_kn_mr_name) "(HknR & Hknr)"; first by apply auth_both_dfrac_valid_2.
    iMod (own_alloc (● (∅ : gsetUR message) ⋅ (◯ (∅ : gsetUR message))))
      as (γ_srv_kn_mt_name) "(HknT & Hknt)"; first by apply auth_both_dfrac_valid_2.
    set (γSgn := ServerGhostNames
                   γ_srv_kn_s_name γ_srv_kn_mr_name γ_srv_kn_mt_name).
    iExists (@chan_mapsto_resource_instance _ _ _ _ _ chanG_instance_0).
    iExists γSgn.
    iExists (@session_resources_instance Mdl Σ _ _ chanG_instance_0 _ _).
    iFrame.
    iModIntro.
    iSplitL. { iPureIntro. apply make_client_skt_spec_holds. }
    iSplitL. { iPureIntro. apply make_server_skt_spec_holds. }
    iSplitL. { iPureIntro. apply (make_connect_skt_spec_holds). }
    iSplitL. { iPureIntro. apply server_listen_spec_holds. }
    iSplitL. { iPureIntro. apply accept_spec_holds. }
    iSplitL. { iPureIntro. apply send_spec_holds. }
    iSplitL. { iPureIntro. apply send_tele_spec_holds. }
    iSplitL. { iPureIntro. apply try_recv_spec_holds. }
    iPureIntro. apply recv_spec_holds.
  Qed.

  Global Instance relcom_init : @Reliable_communication_init _ _ _.
  Proof.
    split.
    intros E UP Hn.
    iStartProof.
    iMod (Reliable_communication_init_instance E UP Hn $! I) as "Hinit".
    iIntros (_).
    iModIntro.
    iDestruct "Hinit" as (???) "Hinit".
    eauto with iFrame.
  Qed.

End Init_initialisation.

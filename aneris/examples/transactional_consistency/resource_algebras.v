From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.bi.lib Require Import fractional.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events.
From aneris.examples.transactional_consistency Require Import aux_defs user_params state_based_model.
Import gen_heap_light.
Import lock_proof.
From aneris.examples.reliable_communication.spec Require Import ras.

Class IDBG Σ :=
  {
    (** Key-Value store *)
    IDBG_Global_mem :> ghost_mapG Σ Key (list write_event);
    IDBG_Global_mono :> inG Σ (authR (gmapUR Key (max_prefix_listR write_eventO)));
    IDBG_Global_snapshots :>
      inG Σ (authR (gmapUR nat (agreeR ((gmapUR Key ((max_prefix_listR write_eventO)))))));

    (** Cache at Client Proxies *)
    IDBG_Cache_phys :> inG Σ (authR (gen_heapUR Key val));
    IDBG_Cache_lgcl :> ghost_mapG Σ Key (option val * bool);
    IDBG_Cache_Msnap :> ghost_mapG Σ Key (list write_event);
    IDBG_TksExcl :> inG Σ (exclR unitO);
    IDBG_ConnectedClients :>
      inG Σ (authR (gmapUR socket_address (agreeR (leibnizO gname))));
    IDBG_TksAgr :>  inG Σ (csumR
                             (exclR unitR)
                             (agreeR ((gnameO * gnameO * gnameO * gnameO * gnameO * gnameO) : Type)));

    (** Time *)
    IDBG_TimeStamp :> mono_natG Σ;
    IDBG_TimeSnaps :> inG Σ (authUR (gsetUR nat));

    (** Lock *)
    IDBG_lockG :> lockG Σ;

    (** Implication Encodings *)
    IDBG_Encoding1 :> inG Σ (authR (gmapUR Key (gsetUR val)));
    IDBG_Encoding2 :> ghost_mapG Σ Key (gset val);

    (** Trace proofs *)
    IDBG_Trace1 :> ghost_mapG Σ socket_address (local_state * option val);
    IDBG_Trace2 :> ghost_mapG Σ socket_address (gname * val);
    IDBG_Trace3 :> ghost_mapG Σ string bool;
    IDBG_Trace4 :> ghost_mapG Σ Key (option val);
    IDBG_Trace5 :> inG Σ (authR (gmapUR nat (agreeR (leibnizO transaction))));
    IDBG_Trace6 :> ghost_mapG Σ Key (list val);
    IDBG_Trace7 :> ghost_mapG Σ socket_address (option (gname * gname * val));
    IDBG_Trace8 :> ghost_mapG Σ socket_address (option val);
    IDBG_Trace9 :> inG Σ (dfrac_agreeR (gmapO Key eventO));
    IDBG_Trace10 :> inG Σ (mono_listUR (leibnizO (transaction * state)));
    IDBG_Trace11 :> inG Σ (mono_listUR (leibnizO val));
    IDBG_Trace12 :> ghost_mapG Σ Key bool;
  }.

Notation KVSG Σ := (IDBG Σ).
 
Definition KVSΣ : gFunctors :=
  #[
      ghost_mapΣ Key (list write_eventO);
      ghost_mapΣ Key (option val * bool);
      GFunctor (authR (gmapUR Key (max_prefix_listR write_eventO)));
      GFunctor ((authR (gen_heapUR Key val)));
      GFunctor (authR (gmapUR nat (agreeR (gmapUR Key (max_prefix_listR write_eventO)))));
      GFunctor
        (authR (gmapUR socket_address (agreeR (leibnizO gname))));
      GFunctor ((csumR
                   (exclR unitR)
                   (agreeR ((gnameO * gnameO * gnameO * gnameO * gnameO * gnameO) : Type))));
     GFunctor (exclR unitO);
     GFunctor (authUR (gsetUR nat));
     GFunctor (authR (gmapUR Key (gsetUR val)));
     ghost_mapΣ Key (gset val);
     ghost_mapΣ socket_address (local_state * option val);
     ghost_mapΣ socket_address (gname * val);
     ghost_mapΣ string bool;
     ghost_mapΣ Key (option val);
     GFunctor (authR (gmapUR nat (agreeR (leibnizO transaction))));
     ghost_mapΣ Key (list val);
     ghost_mapΣ socket_address (option (gname * gname * val));
     ghost_mapΣ socket_address (option val);
     ghost_mapΣ Key bool;
     GFunctor (dfrac_agreeR (gmapO Key eventO));
     GFunctor (mono_listUR (leibnizO (transaction * state)));
     GFunctor (mono_listUR (leibnizO val));
     mono_natΣ;
     ras.SpecChanΣ;
     lockΣ].

Instance subG_KVSΣ {Σ} : subG KVSΣ Σ → KVSG Σ.
Proof. econstructor; solve_inG. Qed.
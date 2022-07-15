From iris.algebra Require Import auth gmap excl excl_auth.
From iris.algebra.lib Require Import mono_list.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources.


Class DBG `{!DB_time} Σ :=
  { DBG_Global_mem :> inG Σ (authR (gen_heapUR Key (option we)));
    DBG_Global_history_mono :> inG Σ (mono_listUR (leibnizO we));
    DBG_Known_replog :> inG Σ (authR (gmapUR socket_address (agreeR gnameO)));
    (* DBG_free_replogG :> inG Σ (gset_disjUR socket_address); *)
    DBG_lockG :> lockG Σ;
    DBG_known_replog_name : gname;
    (* DBG_free_replog_set_name : gname; *)
  }.

Class DBPreG `{!DB_time} Σ :=
  { DB_preG_Global_mem :> inG Σ (authR (gen_heapUR Key (option we)));
    DB_preG_Global_history_mono :> inG Σ (mono_listUR (leibnizO we));
    DB_preG_Known_replog :>
      inG Σ (authR (gmapUR socket_address (agreeR gnameO)));
    (* DB_preG_free_replogG :> inG Σ (gset_disjUR socket_address); *)
    DB_preG_lockG :> lockG Σ;
  }.

Definition DBΣ `{!DB_time} : gFunctors :=
  #[GFunctor (authR (gen_heapUR Key (option we)));
    GFunctor (mono_listUR (leibnizO we));
    GFunctor (authR (gmapUR socket_address (agreeR gnameO)));
    (* GFunctor (gset_disjUR socket_address); *)
    lockΣ].

Instance subG_DB_preGΣ `{!DB_time, !lockG Σ} : subG DBΣ Σ → DBPreG Σ.
Proof. solve_inG. Qed.

From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources.


Class DBG `{!DB_time, !DB_events} Σ :=
  {
    DBG_Global_mem_excl :>
      inG Σ (authUR (gmapUR Key (prodR fracR (agreeR (optionO (leibnizO we))))));
    DBG_Global_history_mono :>
      inG Σ (authUR (monotoneUR (@prefix (leibnizO we))));
    DBG_Local_history_mono :>
      inG Σ (gmapUR socket_address (agreeR gnameO));
    DBG_lockG :>
      lockG Σ;
    DBG_followers_gname : gname;

}.

Class DBPreG `{!DB_time, !DB_events} Σ :=
  {
    DBG_preGlobal_mem_excl :>
      inG Σ (authUR (gmapUR Key (prodR fracR (agreeR (optionO (leibnizO we))))));
    DBG_preGlobal_history_mono :>
      inG Σ (authUR (monotoneUR (@prefix (leibnizO we))));
    DBG_preLocal_history_mono :>
      inG Σ (gmapUR socket_address (agreeR gnameO));
    DBG_prelockG :>
      lockG Σ;
}.


Definition DBΣ `{!DB_time, !DB_events} : gFunctors :=
  #[GFunctor (authUR (gmapUR Key (prodR fracR (agreeR (optionO (leibnizO we))))));
    GFunctor (authUR (monotoneUR (@prefix (leibnizO we))));
    GFunctor (gmapUR socket_address (agreeR gnameO));
    lockΣ].

Instance subG_DB_preGΣ `{!DB_time, !DB_events, !lockG Σ} : subG DBΣ Σ → DBPreG Σ.
Proof. solve_inG. Qed.

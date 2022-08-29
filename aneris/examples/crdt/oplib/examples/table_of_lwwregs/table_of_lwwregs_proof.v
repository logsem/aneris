From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.lwwreg Require Import lwwreg_code lwwreg_proof.
From aneris.examples.crdt.oplib.examples.map_comb Require Import map_comb_code map_comb_proof.
From aneris.examples.crdt.oplib.examples.table_of_lwwregs Require Import table_of_lwwregs_code.

Section table_of_lwwregs_proof.
  Context `{!EqDecision vl, !Countable vl}.
  Context `{!Inject vl val}.
  Context `{!∀ p : vl, Serializable vl_serialization $ p}.
  Context `{!anerisG M Σ, !CRDT_Params, !OpLib_Res (mapOp (LWWOp vl))}.

  Notation map_OpLib_Params' := (@map_OpLib_Params (LWWOp vl) _ _ _ _).
  Notation map_init_st_fn_spec' := (@map_init_st_fn_spec (LWWOp vl)).
  Notation map_effect_spec' := (@map_effect_spec (LWWOp vl)).

  Lemma table_of_lwwregs_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _ _ map_OpLib_Params' table_of_lwwregs_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /table_of_lwwregs_init_st.
    wp_pure _.
    wp_apply map_init_st_fn_spec'; done.
  Qed.

  Lemma table_of_lwwregs_effect_spec :
    ⊢ @effect_spec _ _ _ _ _ _ _ map_OpLib_Params' table_of_lwwregs_effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /table_of_lwwregs_effect.
    wp_pures.
    rewrite /map_comb_effect.
    do 4 wp_pure _.
    wp_apply map_effect_spec';
      [iApply lww_register_init_st_fn_spec|iApply lww_register_effect_spec|done|done].
  Qed.

  Lemma table_of_lwwregs_crdt_fun_spec :
    ⊢ @crdt_fun_spec _ _ _ _ _ _ _ map_OpLib_Params' table_of_lwwregs_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /table_of_lwwregs_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply table_of_lwwregs_init_st_fn_spec; done.
    - iApply table_of_lwwregs_effect_spec; done.
  Qed.

  Notation oplib_init' :=
    (oplib_init
       (s_ser (s_serializer (@OpLib_Serialization _ _ _ _ map_OpLib_Params')))
       (s_deser (s_serializer (@OpLib_Serialization _ _ _ _ map_OpLib_Params')))).

  Lemma table_of_lwwregs_init_spec :
    @init_spec _ _ _ _ _ _ _ map_OpLib_Params' _ _ oplib_init' -∗
    @init_spec_for_specific_crdt _ _ _ _ _ _ _ map_OpLib_Params' _ _
      (table_of_lwwregs_init
         (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /table_of_lwwregs_init /table_of_lwwregs_crdt.
    wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply table_of_lwwregs_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End table_of_lwwregs_proof.

From aneris.aneris_lang Require Import resources proofmode.
From iris.algebra Require Import auth csum excl agree.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.
From iris.base_logic.lib Require Import invariants.

From aneris.examples.crdt.statelib.resources
  Require Import utils resources_inv resources_local resources_global.

Section AboutLock.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.

  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition OwnLockInv (i: RepId) (h__local h__foreign: event_set CRDT_Op): iProp Σ :=
    ∃ (f: fRepId),
      ⌜ fin_to_nat f = i ⌝
      ∗ ⌜ local_events i h__local ⌝
      ∗ ⌜ foreign_events i h__foreign ⌝
      ∗ own (γ_loc_own !!! f) ((1/3)%Qp, to_agree h__local)
      ∗ own (γ_loc_for !!! f) ((1/2)%Qp, to_agree h__foreign).

End AboutLock.


(** TODO: move in utils / utils-like file *)
Section BlahBlah.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.

  Lemma test E repId st_h__local st_h__foreign :
    ⌜ ↑CRDT_InvName ⊆ E ⌝ -∗
    StLib_GlobalInv -∗
    OwnLockInv repId st_h__local st_h__foreign ={E,E}=∗
    OwnLockInv repId st_h__local st_h__foreign
    ∗ StLib_OwnGlobalSnap (st_h__local ∪ st_h__foreign).
  Proof.
    iIntros (?) "Hinv
    (%f & %Hf & %Hf_locisloc & %Hf_forisfor & Hf_own_local & Hf_own_foreign)".
    iInv "Hinv" as "> (%g & Hglobal & Hg_snap & %Hv & Hg_local)" "Hclose".
    iDestruct ((forall_fin f) with "Hg_local")
      as "[Hothers (%st_h__local' & %st_h__foreign' & %st_h__sub &
        %Hf_proj & %Hlocisloc & %Hforisfor & %Hsubisfor & %Hcc &
        Hf_own_local' & Hf_own_foreign' & Hf_own_sub' & Hown_cc)]".
    iDestruct (both_agree_agree with "Hf_own_local Hf_own_local'")
      as "(Hf_own_local & Hf_own_local' & <-)".
    iDestruct (both_agree_agree with "Hf_own_foreign Hf_own_foreign'")
      as "(Hf_own_foreign & Hf_own_foreign' & <-)".

    iDestruct (own_update γ_global_snap (● g.1) (● g.1 ⋅ ◯ (st_h__local ∪ st_h__foreign))
      with "Hg_snap")
      as "> [Hg_snap H2]".
    { apply auth_update_alloc.
      assert (st_h__local ∪ st_h__foreign ⊆ g.1).
      { rewrite -Hf_proj. intros x. by apply gst_valid_inclusion. }
      admit. }

    iDestruct ((forall_fin' f) with "[$Hothers Hown_cc Hf_own_local' Hf_own_foreign' Hf_own_sub']") as "HS".
    { iExists st_h__local, st_h__foreign, st_h__sub. by iFrame. }
    iMod ("Hclose" with "[Hg_snap Hglobal HS]") as "_"; last iModIntro.
    { iNext. iExists g.
      by iFrame. }
    iFrame.
    iExists f. iFrame "%". iFrame.
  Admitted.

End BlahBlah.


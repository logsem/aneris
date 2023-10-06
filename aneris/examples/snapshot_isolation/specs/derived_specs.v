From iris.algebra Require Import auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
  Require Import serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From aneris.examples.snapshot_isolation.specs
  Require Import
  user_params time events aux_defs resource_algebras resources specs.

Set Default Proof Using "Type".

Section Specs.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ,  !KVSG Σ}.

  Definition OwnMemKeyVal (k : Key) (vo : option val) : iProp Σ :=
    ∃ (hv : list val), OwnMemKey k hv ∗ ⌜last hv = vo⌝.

  Inductive TxtSt : Type := TxtCanStart : TxtSt | TxtActive : TxtSt.

  Definition ConnectionStateTxt c sa (st : TxtSt) : iProp Σ :=
    (⌜st = TxtCanStart⌝ ∗  ConnectionState c sa CanStart) ∨
    (⌜st = TxtActive⌝ ∗ ∃ ms,  ConnectionState c sa (Active ms)).

  Definition commitTxt (p : option val * bool) (w : option val) :=
    match p with
    | (Some v, true) => Some v
    | _              => w
    end.



  Lemma convert_mhist (m : gmap Key (option val)) :
    ([∗ map] k↦vo ∈ m, ∃ hv : list val, k ↦ₖ hv ∗ ⌜last hv = vo⌝) ⊣⊢
      ∃ (mh : gmap Key (list val)),
        ⌜m = (last)<$> mh⌝ ∗ ([∗ map] k↦h ∈ mh, k ↦ₖ h).
  Proof.
  Admitted.
                                                              
 Lemma start_spec_derived : 
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
       IsConnected c sa -∗
       ⌜start_spec⌝ -∗ 
    <<< ∀∀ (m : gmap Key (option val)),
       ConnectionStateTxt c sa TxtCanStart ∗
       [∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionStateTxt c sa TxtActive ∗
       ([∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo) ∗
       ([∗ map] k ↦ vo ∈ m, k ↦{c} vo ∗ KeyUpdStatus c k false) >>>.
  Proof.
    iIntros (c sa E HE) "#Hic %spec".
    iIntros (Φ) "!# Hsh".
    wp_apply (spec _ _ E with "[//][//][Hsh]").
    iMod "Hsh".
    iModIntro.
    iDestruct "Hsh" as (m) "((Hst & Hkeys) & Hsh)".
    rewrite /OwnMemKeyVal /Hist.
    rewrite convert_mhist.
    iDestruct "Hkeys" as (mh Heq) "Hkeys".
    iExists mh.
    rewrite /ConnectionStateTxt.
    iDestruct "Hst" as "[(_ & Hres)|(%df & _)]"; last done.
    iFrame.
    iNext.
    iIntros "(Hst & Hks & (Hres & _))".
    iApply ("Hsh" with "[Hst Hks Hres]").
    iSplitL "Hst"; first eauto.
    rewrite Heq.
    iSplitL "Hks".
    by iExists mh; iSplit; first done.
    by rewrite big_sepM_fmap.
  Qed.
  
  Lemma commit_spec_derived :
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
     ⌜↑KVS_InvName ⊆ E⌝ -∗
       IsConnected c sa -∗
       ⌜commit_spec⌝ -∗ 
    <<< ∀∀ (m : gmap Key (option val))
           (mc : gmap Key (option val * bool)),
        ConnectionStateTxt c sa TxtActive ∗
        ⌜dom m = dom mc⌝ ∗
        ([∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionStateTxt c sa TxtCanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗  
          ([∗ map] k↦ vo;p ∈ m; mc, OwnMemKeyVal k (commitTxt p vo))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗
           [∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo)) >>>.
  Proof.
  Admitted.

 
 End Specs.

(** Realisation of the RCB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting inject.
From aneris.aneris_lang.lib Require Import list_proof map_proof vector_clock_proof lock_proof queue_proof.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import model_lst model_spec.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst.
From aneris.examples.rcb.util Require Import list_proof_alt.

Import ast.

Section Local_invariant.
  Context `{anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.
  Context (γGown γGsnap : gname) (γLs : list gname).

  Definition InQueue_inv i ip Q (lq : list global_event) vq : iProp Σ :=
    Q ↦[ip] vq ∗
    ⌜is_list lq vq⌝ ∗
    ([∗ list] a ∈ lq,
      ⌜not (a.(ge_orig) = i)⌝ ∗
      own_global_snap γGsnap {[ a ]}).

  Definition single_queue_inv i (lq : list global_event) : iProp Σ :=
    [∗ list] ge ∈ lq, ⌜RCB_Serializable (ge_payload ge)⌝ ∗
                       own_global_snap γGsnap {[ ge ]} ∗
                       ⌜not (ge.(ge_orig) = i)⌝ ∗
                       ⌜∃ orig_addr, RCB_addresses !! ge.(ge_orig) = Some orig_addr⌝.

  Definition OutQueues_inv ip (Q : loc) (lqs : list (list global_event)) (vqs : val) : iProp Σ :=
    Q ↦[ip] vqs ∗
    ⌜is_listP lqs vqs is_queue⌝ ∗
    ⌜length lqs = length RCB_addresses⌝ ∗
    ([∗ list] i ↦ lq ∈ lqs, single_queue_inv i lq)%I.

  Definition local_inv_def (i : nat) (T SeenLoc IQ OQ : loc) : iProp Σ :=
    ∃ (vt vseen viq voq : val)
      (t seen: vector_clock)
      (liq : list global_event)
      (loq : list (list global_event))
      (s : gset local_event)
      (ip : ip_address),
        ⌜ip_of_address <$> RCB_addresses !! i = Some ip⌝ ∗
        T ↦[ip] vt ∗
        ⌜is_vc vt t⌝ ∗
        SeenLoc ↦[ip] vseen ∗
        ⌜is_vc vseen seen⌝ ∗
        (* TODO: should we move this to be part of local state validity below *)
        ⌜length seen = length t⌝ ∗
        InQueue_inv i ip IQ liq viq ∗
        OutQueues_inv ip OQ loq voq ∗
        lhst_lock γLs i s ∗
        ⌜RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s|}⌝.

  Definition local_invariant
             (i : nat) (T SeenLoc InQueue OutQueues : loc) (lk : val)
             (γlk : gname) (z : socket_address) : iProp Σ :=
    is_lock (nroot.@"lk") (ip_of_address z) γlk lk
            (local_inv_def i T SeenLoc InQueue OutQueues).

  Instance local_invariant_persistent i IQ OQ T SeenLoc lk γLk z :
    Persistent (local_invariant i T SeenLoc IQ OQ lk γLk z).
  Proof. apply _. Qed.

  Lemma single_queue_inv_dup_front i ge lq :
    single_queue_inv i (ge :: lq) ⊢
                     single_queue_inv i (ge :: lq) ∗
                     ⌜RCB_Serializable ge.(ge_payload)⌝ ∗
                     own_global_snap γGsnap {[ ge ]} ∗
                     ⌜not (ge.(ge_orig) = i)⌝ ∗
                     ⌜∃ orig_addr : socket_address, RCB_addresses !! ge.(ge_orig) = Some orig_addr⌝.
  Proof.
    iIntros "Hown".
    iDestruct (big_sepL_cons with "Hown") as "[[#Hser #Hsnap] Ht]".
    iFrame "#"; iFrame.
  Qed.

  Lemma single_queue_inv_tail i ge lq :
    single_queue_inv i (ge :: lq) ⊢ single_queue_inv i lq.
  Proof.
    iIntros "Hown".
    iDestruct (big_sepL_cons with "Hown") as "[[#Hser #Hsnap] Ht]".
    eauto with iFrame.
  Qed.

End Local_invariant.

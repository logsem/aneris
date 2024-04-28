From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.dscm.spec Require Import base time events resources init.

(*
0. FreeProxy token. client proxy
1. Define resources carrying pre, vs, and posts of write and read specs.
2. Define socket protocol for server and proxy. *)

Section Resources.
  Context `{!anerisG Mdl Σ, !DB_time, !DB_events}.

  Class DB_internal_communicationG := {
    freeProxyTokenG :> inG Σ (gset_disjUR socket_address) ;
    write_postG :> (savedPredG Σ (we * ghst));
    read_postG :> (savedPredG Σ (option we * ghst));
    seqIddG :> inG Σ (authR (gmapUR nat (agreeR (leibnizO (gname + gname)))));
    known_clients_name : gname; (* saddr -> gname *)
    known_clientsG :> inG Σ (authR (gmapUR socket_address (agreeR gnameO)));
    free_clients_set_name : gname;
    free_clientsG :> inG Σ (gset_disjUR socket_address);
    }.

  Class DB_internal_communicationPreG := {
    freeProxyTokenPreG :> inG Σ (gset_disjUR socket_address) ;
    write_postPreG :> (savedPredG Σ (we * ghst));
    read_postPreG :> (savedPredG Σ (option we * ghst));
    seqIdPreG :> inG Σ (authR (gmapUR nat (agreeR (leibnizO (gname + gname)))));
    known_clientsPreG :> inG Σ (authR (gmapUR socket_address (agreeR gnameO)));
    free_clientsPreG :> inG Σ (gset_disjUR socket_address);
    }.


  Definition DB_internal_communicationΣ : gFunctors :=
    #[GFunctor (gset_disjUR socket_address);
      savedPredΣ (we * ghst);
      savedPredΣ (option we * ghst);
      GFunctor (authUR (gmapUR nat (agreeR (leibnizO (gname + gname)))));
     GFunctor (authUR (gmapUR socket_address (agreeR gnameO)));
     GFunctor (authUR (gset_disjUR socket_address))
     ].

  Global Instance subG_DB_internal_communicationPreG :
    subG (DB_internal_communicationΣ) Σ → DB_internal_communicationPreG.
  Proof. constructor; solve_inG. Qed.

End Resources.

Global Arguments DB_internal_communicationG _ {_ _}.
Global Arguments DB_internal_communicationPreG _ {_ _}.

Section Definitions_Lemmas.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.
  Context `{!DB_internal_communicationG Σ}.

  Definition free_client_proxy (sa : socket_address) : iProp Σ :=
    own free_clients_set_name (GSet {[sa]}).

  Definition known_client (sa : socket_address) (γmap : gname) : iProp Σ :=
    own known_clients_name (◯ {[ sa := to_agree γmap ]}).

  Definition known_clients (M : gmap socket_address gname) : iProp Σ :=
    own free_clients_set_name (GSet (dom M)) ∗
    own known_clients_name (● (to_agree <$> M : gmap _ _)).

  Definition client_requests (sa : socket_address) (n : nat) : iProp Σ :=
    ∃ γ M, known_client sa γ ∗ 
          own (A := (authUR (gmapUR nat (agreeR (leibnizO (gname + gname)))))) 
            γ (● (to_agree <$> M )) ∗ ⌜dom M = set_seq 0 n⌝.

  Definition client_req (sa : socket_address) (id : nat) (req : sum gname gname) : iProp Σ :=
    ∃ γ, known_client sa γ ∗ own γ (◯ {[id := to_agree req]}).

  Lemma free_client_proxy_exclusive sa : free_client_proxy sa -∗ free_client_proxy sa -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%gset_disj_valid_op.
    set_solver.
  Qed.

  (* just as examples ... *)
  (* Definition read_post_is (γ : gname) (Ψ : option we * ghst → iProp Σ) := saved_pred_own γ Ψ. *)
  (* Definition write_post_is (γ : gname) (Ψ : we * ghst → iProp Σ) := saved_pred_own γ Ψ. *)

  Global Instance known_client_Persistent sa γ : Persistent (known_client sa γ).
  Proof. apply _. Qed.
  Global Instance known_client_Timeless sa γ : Timeless (known_client sa γ).
  Proof. apply _. Qed.
  Global Instance free_client_proxy_Timeless sa : Timeless (free_client_proxy sa).
  Proof. apply _. Qed.

  Lemma known_client_agree sa γ γ' : known_client sa γ -∗ known_client sa γ' -∗ ⌜γ = γ'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    apply auth_frag_op_valid_1 in Hvl.
    specialize (Hvl sa).
    rewrite !lookup_op !lookup_singleton -Some_op in Hvl.
    revert Hvl; rewrite Some_valid; intros ?%to_agree_op_valid%leibniz_equiv; done.
  Qed.

  Lemma introduce_client M sa :
    known_clients M -∗ free_client_proxy sa ==∗
    ∃ γ, ⌜sa ∉ dom M⌝ ∗ known_clients (<[sa := γ]>M) ∗ client_requests sa 0.
  Proof.
    iIntros "[HM1 HM2] Hsa".
    iMod (own_alloc (A := (authUR (gmapUR nat (agreeR (leibnizO (gname + gname)))))) 
                    (● (to_agree <$> ∅ : gmap nat _))) as (γ) "H";
      first by apply auth_auth_valid.
    iAssert (⌜sa ∉ dom M⌝)%I as %?.
    { destruct (decide (sa ∈ dom M)); last done.
      iClear "HM2".
      replace (dom M) with ({[sa]} ∪ dom M ∖ {[sa]}); last first.
      { apply set_eq; intros x; split; first set_solver. destruct (decide (x = sa)); set_solver. }
      rewrite -gset_disj_union; last set_solver.
      iDestruct "HM1" as "[HM1 _]".
      iDestruct (free_client_proxy_exclusive with "HM1 Hsa") as "?"; done. }
    iAssert (own free_clients_set_name (GSet (dom (<[sa := γ]>M))))
      with "[HM1 Hsa]" as "HM1".
    { rewrite insert_union_singleton_l dom_union_L dom_singleton_L.
      rewrite -gset_disj_union; last set_solver.
      rewrite own_op; iFrame. }
    iMod (own_update _ _ (● (to_agree <$> (<[sa := γ]>M) : gmap _ _) ⋅ (◯ {[sa := to_agree γ]}))
            with "HM2") as "[HM2 Hnew]".
    { rewrite fmap_insert. apply auth_update_alloc, alloc_local_update; last done.
      apply not_elem_of_dom; rewrite dom_fmap; done. }
    iModIntro; iExists _; iFrame.
    iSplitR; first done.
    iExists γ, ∅; iFrame.
    rewrite dom_empty_L; done.
  Qed.

  Global Instance client_req_persistent sa n req : Persistent (client_req sa n req).
  Proof. apply _. Qed.
  Global Instance client_req_timeless sa n req : Timeless (client_req sa n req).
  Proof. apply _. Qed.

  Lemma client_req_agree sa n req req' :
    client_req sa n req -∗ client_req sa n req' -∗ ⌜req = req'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (γ1) "[H11 H12]".
    iDestruct "H2" as (γ) "[H21 H22]".
    iDestruct (known_client_agree with "H11 H21") as %->.
    iDestruct (own_valid_2 with "H12 H22") as %Hvl.
    apply auth_frag_op_valid_1 in Hvl.
    specialize (Hvl n).
    rewrite !lookup_op !lookup_singleton -Some_op in Hvl.
    revert Hvl; rewrite Some_valid to_agree_op_valid; intros ->%leibniz_equiv; done.
  Qed.

  Lemma client_make_req sa n req :
    client_requests sa n ==∗ client_requests sa (S n) ∗ client_req sa n req.
  Proof.
    iDestruct 1 as (γ M) "(#HM1 & HM2 & %HM3)".
    iMod (own_update (A := (authUR (gmapUR nat (agreeR (leibnizO (gname + gname)))))) 
                      _ _ (● (to_agree <$> (<[n := req]>M) : gmap _ _) ⋅ ◯ {[n := to_agree (req : leibnizO (_ + _))]})
            with "HM2") as "[HM2 Hnew]".
    { rewrite fmap_insert. 
      apply auth_update_alloc, alloc_local_update; last done.
      apply not_elem_of_dom; rewrite dom_fmap.
      rewrite HM3 elem_of_set_seq; lia. }
    iModIntro.
    iSplitL "HM2".
    - iExists _, _; iFrame; iFrame "#".
      rewrite dom_insert_L set_seq_S_end_union_L /= HM3; done.
    - by iExists _; iFrame.
  Qed.

End Definitions_Lemmas.

Lemma init_clients `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}
      `{!DB_internal_communicationPreG Σ}  (N : gset socket_address) :
  ⊢ |==> ∃ `(!DB_internal_communicationG Σ), known_clients ∅ ∗ [∗ set] sa ∈ N, free_client_proxy sa.
Proof.
  iIntros "".
  iMod (own_alloc (● (∅ : gmap socket_address _))) as (γ) "H1"; first by apply auth_auth_valid.
  iMod (own_alloc (GSet N)) as (γ') "H2"; first done.
  replace N with (N ∪ ∅) at 1 by set_solver.
  rewrite -gset_disj_union; last set_solver.
  iDestruct "H2" as "[H21 H22]".
  iModIntro.
  iExists {| free_clients_set_name := γ'; known_clients_name := γ |}.
  iSplitL "H1 H22".
  - rewrite /known_clients dom_empty_L fmap_empty; iFrame.
  - iInduction N as [|x N] "IH" using set_ind_L; first done.
    rewrite big_sepS_insert; last done.
    rewrite -gset_disj_union; last set_solver.
    iDestruct "H21" as "[$ H21]".
    iApply "IH"; done.
Qed.

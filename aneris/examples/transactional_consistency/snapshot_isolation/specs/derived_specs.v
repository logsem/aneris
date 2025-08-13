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
From aneris.examples.transactional_consistency.snapshot_isolation
  Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.util
     Require Import util_code util_proof.
From aneris.examples.transactional_consistency.snapshot_isolation.specs
  Require Import
  time events aux_defs resources specs.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
  Require Import
  snapshot_isolation_api_implementation.

Set Default Proof Using "Type".

Section DerivedSpecs.

  (* OBS: This is only a proof that the full specications for SI imply the derived
    specificton for SI with the given resource defintions, 
    not a full proof of implication between specication-packages, 
    see e.g. RC_implies_RC.v  *)

  Import code_api.
  
  Context `{!anerisG Mdl Σ, !User_params, !SI_resources Mdl Σ,  !KVSG Σ}.

  Definition OwnMemKeyVal (k : Key) (vo : option val) : iProp Σ :=
    ∃ (hv : list val), OwnMemKey k hv ∗ ⌜last hv = vo⌝.

  Inductive TxtSt : Type :=
  | TxtCanStart : TxtSt
  | TxtActive (m : gmap Key (option val)) : TxtSt.

  Definition ConnectionStateTxt c sa (st : TxtSt) : iProp Σ :=
    (⌜st = TxtCanStart⌝ ∗  ConnectionState c sa CanStart) ∨
    (∃ m, ⌜st = TxtActive m⌝ ∗ ∃ ms, ConnectionState c sa (Active ms) ∗ ⌜last <$> ms = m⌝).

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
    iInduction m as [| k vo m Hk] "IH" using map_ind.
    - iSplit; last by iIntros; done.
      iIntros. iExists ∅. rewrite fmap_empty. by iSplit; first set_solver.
    - iDestruct "IH" as "(IH1 & IH2)".
      iSplit.
      -- iClear "IH2".
         rewrite !big_sepM_insert; last done.
         iIntros "(H1 & H2)".
         iDestruct ("IH1" with "[$H2]") as "H2".
         iDestruct "H2" as (mh) "(%Heq & H2)".
         iDestruct "H1" as (h) "(Hk & %Heqh)".
         iExists (<[k:=h]>mh).
         iSplit.
         --- by iPureIntro; simplify_map_eq /=; rewrite fmap_insert.
         --- rewrite big_sepM_insert; first iFrame.
             rewrite Heq in Hk.
             rewrite lookup_fmap in Hk.
             by destruct (mh !! k) eqn:Hhk; first done.
      -- iClear "IH1".
         rewrite !big_sepM_insert; last done.
         iIntros "H".
         iDestruct "H" as (mh Heq) "Hks".
         assert (∃ h, mh !! k = Some h) as (h & Heqh).
         { destruct (mh !! k) eqn:Heqkh; first eauto.
           apply not_elem_of_dom in Heqkh.
           rewrite -(dom_fmap last) in Heqkh.
           rewrite -Heq in Heqkh.
           set_solver. }
         iDestruct (big_sepM_delete with "Hks") as "(Hk & Hks)"; first done.
         iSplitL "Hk".
         { iExists h. iFrame. iPureIntro. simpl.
           assert (((last <$> mh) !! k) = Some vo) as Ha.
           { rewrite -Heq. by rewrite lookup_insert. }
           rewrite lookup_fmap in Ha.
           rewrite Heqh in Ha.
           apply fmap_Some_1 in Ha.
           set_solver. }
         iApply "IH2".
         iExists (delete k mh).
         iFrame.
         iPureIntro.
         assert (delete k (<[k:=vo]> m) = delete k (last <$> mh)) as Heqdel.
         { f_equal. eauto. }
         rewrite delete_insert in Heqdel; last done.
         by rewrite fmap_delete.
  Qed.

  Lemma init_client_proxy_spec_derived : 
    ∀ (sa : socket_address),
    init_client_proxy_spec -∗
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        KVS_ClientCanConnect sa ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      TC_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionStateTxt cstate sa TxtCanStart ∗
                            IsConnected cstate sa }}}.
  Proof.
    iIntros (sa) "#Hspec !#". 
    iIntros (Φ) "(H_unalloc & H_interp & H_m_hist & H_conn & H_ports) HΦ".
    wp_apply ("Hspec"  with "[$H_unalloc $H_interp $H_m_hist $H_conn $H_ports][HΦ]").
    iNext.
    iIntros (cstate) "(H_state & H_conn)".
    iApply "HΦ".
    iFrame.
    iLeft.
    by iFrame.
  Qed.

 Lemma start_spec_derived : 
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
       IsConnected c sa -∗
       start_spec -∗ 
    <<< ∀∀ (m : gmap Key (option val)),
       ConnectionStateTxt c sa TxtCanStart ∗
       [∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo >>>
      TC_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionStateTxt c sa (TxtActive m) ∗
       ([∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo) ∗
       ([∗ map] k ↦ vo ∈ m, k ↦{c} vo ∗ KeyUpdStatus c k false) >>>.
  Proof.
    iIntros (c sa E HE) "#Hic #spec".
    iIntros (Φ) "!# Hsh".
    wp_apply ("spec" $! _ _ E with "[//][//][Hsh]").
    iModIntro.
    iMod "Hsh".
    iModIntro.
    iDestruct "Hsh" as (m) "((Hst & Hkeys) & Hsh)".
    rewrite /OwnMemKeyVal /Hist.
    rewrite convert_mhist.
    iDestruct "Hkeys" as (mh Heq) "Hkeys".
    iExists mh.
    rewrite /ConnectionStateTxt.
    iDestruct "Hst" as "[(_ & Hres)|Habs]"; last first.
    { iDestruct "Habs" as (_df) "(% & _)". done. }
    iFrame.
    iIntros "(Hst & Hks & (Hres & _))".
    iApply ("Hsh" with "[Hst Hks Hres]").
    iSplitL "Hst"; first eauto.
    rewrite Heq.
    iRight.
    iExists (last <$> mh).
    iSplit; first done.
    by iExists mh; iSplit; first done.
    iSplitL "Hks". iExists _. by iFrame.
    rewrite Heq. by rewrite big_sepM_fmap.
  Qed.
  
  Lemma commit_spec_derived :
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
     ⌜↑KVS_InvName ⊆ E⌝ -∗
       IsConnected c sa -∗
       commit_spec -∗ 
    <<< ∀∀ (m ms : gmap Key (option val))
           (mc : gmap Key (option val * bool)),
        ConnectionStateTxt c sa (TxtActive ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) >>>
      TC_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionStateTxt c sa TxtCanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗  
          ([∗ map] k↦ vo;p ∈ m; mc, OwnMemKeyVal k (commitTxt p vo))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗
           [∗ map] k ↦ vo ∈ m, OwnMemKeyVal k vo)) >>>.
  Proof.
    iIntros (c sa E HE) "#Hic #spec".
    iIntros (Φ) "!# Hsh".
    wp_apply ("spec" $! _ _ E with "[//][//][Hsh]").
    iModIntro.
    iMod "Hsh".
    iModIntro.
    iDestruct "Hsh" as (m ms_ mc) "((Hst & %HdomEq1 & %HdomEq2 & Hkeys1 & Hkeys2) & Hsh)".
    rewrite /OwnMemKeyVal /Hist.
    iDestruct (convert_mhist m with "Hkeys1") as (mh Heqmh) "Hkeys1".
    rewrite /ConnectionStateTxt.
    iDestruct "Hst" as "[(%Habs & _)|Hst]"; first done.
    iDestruct "Hst" as  (_ms) "(%HeqT & (%ms & Hres & %Heq))".
    iExists mh, ms, mc.
    iFrame.
    iSplit.
    { iPureIntro. inversion HeqT; subst. set_solver. }
    iIntros (b) "(Hst & Hpost)".  
    iApply ("Hsh" with "[Hst Hpost]").
    iSplitL "Hst".
    iLeft. iFrame; eauto.
    iDestruct "Hpost" as "[Hp|Hp]"; iDestruct "Hp" as "(-> & (_ & Hkeys))".
    - iLeft; iSplit; first done.
      rewrite Heqmh.
      rewrite big_sepM2_fmap_l.
      iApply (big_sepM2_mono with "Hkeys").
      iIntros (k hk p Hk1 Hc1) "(Hk & _)".
      destruct p as (vo, b)  eqn:Hp;
        destruct vo as [v|] eqn:Hvo;
        destruct b eqn:Hb;
        iExists _; eauto with iFrame.
      simpl. iFrame. by rewrite last_snoc. 
    - iRight; iSplit; first done.
      rewrite Heqmh. rewrite big_sepM_fmap.
      iApply (big_sepM_mono with "Hkeys").
      iIntros (k hk Hk) "(Hk & _)".
      iExists hk. by iFrame.
  Qed.

   Lemma run_spec_derived_generic :
    ∀ (c : val) (tbody : val) (sa : socket_address) (E : coPset)
      (P :  gmap Key (option val) → iProp Σ)
      (Q : (gmap Key (option val)) -> (gmap Key (option val)) -> (gmap Key (option val * bool)) → iProp Σ),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      start_spec -∗
      commit_spec -∗
      IsConnected c sa -∗
      {{{
        ConnectionStateTxt c sa TxtCanStart ∗
        (* Viewshift for looking at the state of the database at start time *)
        (▷ |={⊤, E}=> ∃ m_at_start, P m_at_start ∗ ([∗ map] k ↦ vo ∈ m_at_start, OwnMemKeyVal k vo) ∗ 
           (([∗ map] k ↦ vo ∈ m_at_start, OwnMemKeyVal k vo) ={E, ⊤}=∗ emp )) ∗
        (* Specification for the body of the transaction *)
        (∀ (m_snap : gmap Key (option val)),
          {{{ 
            ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap 
          }}}
            tbody c  @[ip_of_address sa] 
          {{{ (mc : gmap Key (option val * bool)), RET #();
            ⌜dom m_snap = dom mc⌝ ∗
            ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
            (* Viewshift for looking at the state of the database at commit time after
              the transaction body has been executed *)
            (▷ |={⊤, E}=> ∃ m_at_commit, ([∗ map] k ↦ vo ∈ m_at_commit, OwnMemKeyVal k vo) ∗
                ⌜dom m_at_commit = dom m_snap⌝ ∗ Q m_at_commit m_snap mc ∗
                ((([∗ map] k↦ vo;p ∈ m_at_commit; mc, OwnMemKeyVal k (commitTxt p vo)) ∨
                  ([∗ map] k ↦ vo ∈ m_at_commit, OwnMemKeyVal k vo)) ={E, ⊤}=∗ emp))
          }}})
      }}}
       run c tbody @[ip_of_address sa] 
     {{{ m ms mc (b : bool), RET #b;
         ConnectionStateTxt c sa TxtCanStart ∗ Q m ms mc
     }}}.
  Proof.
    iIntros (c bdy sa E P Q HE) "#HspecS #HspecC #HiC !# %Φ (HstS & Hsh1 & #HspecBdy) HΦ".
    rewrite /run.
    wp_pures. wp_apply start_spec_derived; try eauto.
    iMod "Hsh1" as (m_at_start) "(HP & Hks & Hsh1)".
    iModIntro. iExists m_at_start. iFrame.
    iIntros "(HstA & Hmks & Hcks)".
    iMod ("Hsh1" with "[$Hmks]") as "_".
    iModIntro. wp_pures. wp_apply ("HspecBdy" with "[$HP $Hcks]").
    iIntros (mc) "(%Hdeq1 & Hcks & Hsh2)".
    wp_pures. wp_apply commit_spec_derived; try eauto.
    iMod ("Hsh2") as (m_at_commit) "(Hks & %Hdom1 & HQ & Hsh2)".
    iModIntro. iExists _, _, _. iFrame.
    iSplit; [iPureIntro; set_solver|].
    iIntros (b) "(HstS & Hdisj)".
    iApply ("HΦ" $! m_at_commit m_at_start mc).
    iFrame. iDestruct "Hdisj" as "[Hc | Ha]".
    - iDestruct "Hc" as "(%Hbt & Hkts)".
      by iMod ("Hsh2" with "[$Hkts]") as "_".
    - iDestruct "Ha" as "(%Hbf & Hkts)".
      by iMod ("Hsh2" with "[$Hkts]") as "_". 
  Qed.

  Lemma run_spec_derived_simple :
    ∀ (c : val) (tbody : val) (domain : gset Key)
    (sa : socket_address) (E : coPset)
    (P :  gmap Key (option val) → iProp Σ)
    (Q :  gmap Key (option val * bool) → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    start_spec -∗ 
    commit_spec -∗
    IsConnected c sa -∗
    □ (▷ |={⊤, E}=> ∃ m_snap, ⌜dom m_snap = domain⌝ ∗ P m_snap ∗ ([∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo)
      ∗ (((∃ m_cache, Q m_cache ∗ ([∗ map] k↦ vo;p ∈ m_snap; m_cache, OwnMemKeyVal k (commitTxt p vo)))
            ∨ (([∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo))) ={E, ⊤}=∗ emp)) -∗
    (∀ m_snap,
      {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
          tbody c  @[ip_of_address sa]
      {{{ (m_cache : gmap Key (option val * bool)), RET #(); ⌜dom m_snap = dom m_cache⌝ ∗
          ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗ Q m_cache }}}) -∗
    {{{ ConnectionStateTxt c sa TxtCanStart }}}
          run c tbody @[ip_of_address sa] ⊤
    {{{ b, RET #b; ConnectionStateTxt c sa TxtCanStart }}}.
  Proof.
    iIntros (c tbody domain sa E P Q H_sub) 
    "#H_start_spec #H_commit_spec #H_conn #H_shift #H_body".
    iIntros (Φ) "!# H_state HΦ".
    rewrite /run /=.
    wp_pures.
    wp_apply start_spec_derived; try eauto.
    iPoseProof "H_shift" as "H_shift'".
    iMod "H_shift'" as (m_snap_start) "(%H_dom & H_P & H_keys & H_shift')".
    iModIntro.
    iExists m_snap_start.
    iFrame.
    iIntros "(H_state & H_keys & H_cache)".
    iMod ("H_shift'" with "[$H_keys]") as "_".
    iModIntro.
    wp_pures.
    wp_apply ("H_body" $! m_snap_start  with "[$H_cache $H_P]"). 
    iIntros (m_cache) "(%H_dom' & H_cache & H_Q)".
    wp_pures.
    wp_apply commit_spec_derived; try eauto.
    iMod "H_shift" as (m_snap_commit) "(%H_dom'' & H_P & H_keys & H_shift)".
    iModIntro.
    iExists m_snap_commit, m_snap_start, m_cache.
    iFrame.
    iSplit.
    {
      iPureIntro.
      by rewrite H_dom -H_dom'.
    }
    iIntros (b) "(H_state & [(-> & H_keys) | (-> & H_keys)])".
    - iMod ("H_shift" with "[H_keys H_Q]") as "_".
      + iLeft.
        iExists m_cache.
        iFrame.
      + iModIntro.
        by iApply "HΦ".
    - iMod ("H_shift" with "[H_keys]") as "_".
      + by iRight.
      + iModIntro.
        by iApply "HΦ".
  Qed.

End DerivedSpecs.

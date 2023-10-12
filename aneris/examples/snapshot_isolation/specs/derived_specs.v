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
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
  Require Import
  user_params time events aux_defs resource_algebras resources specs.
From aneris.examples.snapshot_isolation.instantiation
  Require Import
  snapshot_isolation_api_implementation.

Set Default Proof Using "Type".

Section Specs.

  Import snapshot_isolation_code_api.
  
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
  
  Definition SeenVal (k : Key) (vo : option val) : iProp Σ :=
    ∃ (h : list val) (v : val),
      ⌜last h = vo⌝ ∗ ⌜vo = Some v⌝ ∗ Seen k h.

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
       ConnectionStateTxt c sa (TxtActive m) ∗
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
    iDestruct "Hst" as "[(_ & Hres)|Habs]"; last first.
    { iDestruct "Habs" as (_df) "(% & _)". done. }
    iFrame.
    iNext.
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
       ⌜commit_spec⌝ -∗ 
    <<< ∀∀ (m ms : gmap Key (option val))
           (mc : gmap Key (option val * bool)),
        ConnectionStateTxt c sa (TxtActive ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
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
    iIntros (c sa E HE) "#Hic %spec".
    iIntros (Φ) "!# Hsh".
    wp_apply (spec _ _ E with "[//][//][Hsh]").
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
    iNext.
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

  (* This us not intuitive to read because the viewshift seems backwards, 
      because the viewshifts from the atomicity notation is used together 
      with the other viewshifts. But the atomicity notation makes it cleaner
      to talk about the return value. Also the persistent modality around 
      does not seem to be needed. *)
  Lemma run_spec_derived_candidate_1 :
    ∀ (c : val) (tbody : val)
    (sa : socket_address) (E : coPset)
    (P :  gmap Key (option val) → iProp Σ)
    (Q :  gmap Key (option val) →
          gmap Key (option val * bool) → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜start_spec⌝ -∗ 
    ⌜commit_spec⌝ -∗
    IsConnected c sa -∗
    (∀ (m_snap : gmap Key (option val)),
        {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
            tbody c  @[ip_of_address sa] 
        {{{ (m_cache : gmap Key (option val * bool)), RET #();
            ⌜dom m_snap = dom m_cache⌝ ∗
            ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
              Q m_snap m_cache }}}) -∗
      □ (∀ m_snap,
          ([∗ map] k↦vo ∈ m_snap, OwnMemKeyVal k vo) ={E, ⊤}=∗ 
            |={⊤,E}=> ∃ m_new, ⌜dom m_new = dom m_snap⌝ ∗
          (([∗ map] k ↦ vo ∈ m_new, OwnMemKeyVal k vo))) -∗
    <<< ∀∀ m_snap, ConnectionStateTxt c sa TxtCanStart ∗
            P m_snap ∗ [∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo >>>
        SI_run c tbody @[ip_of_address sa] E
    <<<▷∃∃ m_new mc b, RET #b;
      ConnectionStateTxt c sa TxtCanStart ∗
      (** Transaction has been commited. *)
      ((⌜b = true⌝ ∗ Q m_snap mc ∗
        ([∗ map] k↦ vo;p ∈ m_new; mc, OwnMemKeyVal k (commitTxt p vo))) ∨
      (** Transaction has been aborted. *)
      (⌜b = false⌝ ∗
        [∗ map] k ↦ vo ∈ m_new, OwnMemKeyVal k vo)) >>>.
Proof.
  iIntros (c tbody sa E P Q HE HspecS HspecC).
  iIntros "#HiC #Hbody #pre_body".
  iIntros (Φ) "!# Hsh".
  rewrite /SI_run /= /run.
  wp_pures.
  wp_apply start_spec_derived; try eauto.
  iMod "Hsh".
  iDestruct "Hsh" as (m_snap) "((Hst & HP & Hks) & Hsh)".
  iModIntro.
  iExists m_snap.
  iFrame.
  iNext. 
  iIntros "(Hst & Hks & Hcs)".
  iMod ("pre_body" $! m_snap with "[$Hks]") as "Hcl".
  iModIntro.
  wp_pures.
  wp_apply ("Hbody" $! m_snap  with "[$Hcs $HP]"). 
  iIntros (m_cache) "(%Hdom & Hcache & HQ)".
  wp_pures.
  wp_apply commit_spec_derived; try eauto.
  iMod "Hcl" as (m_new) "(%Hdom' & Hks)".
  iModIntro.
  iExists m_new, m_snap, m_cache.
  iFrame.
  iSplit; first by iPureIntro; set_solver.
  iNext.
  iIntros (b) "(Hst & Hpost)".
  iMod ("Hsh" $! m_new m_cache b with "[HQ $Hst Hpost]").
  iDestruct "Hpost" as "[(-> & Hpost) | (-> & Hpost)]".
  - iLeft. by iFrame.
  - iRight. by iFrame.
  - done.
Qed.

(* Lemma run_spec_derived_generic :
  ∀ (c : val) (tbody : val)
  (sa : socket_address) (E : coPset)
  (R1 : (gmap Key (option val)) -> (gmap Key (option val * bool)) → iProp Σ) (R2 : iProp Σ)
  (P :  gmap Key (option val) → iProp Σ)
  (Q :  gmap Key (option val) →
        gmap Key (option val * bool) → iProp Σ),
  ⌜↑KVS_InvName ⊆ E⌝ -∗
  ⌜start_spec⌝ -∗ 
  ⌜commit_spec⌝ -∗
  IsConnected c sa -∗
  (|={⊤, E}=> ∃ m_start, P m_start ∗ ([∗ map] k ↦ vo ∈ m_start, OwnMemKeyVal k vo) 
        ∗ ▷ (([∗ map] k ↦ vo ∈ m_start, OwnMemKeyVal k vo) ={E, ⊤}=∗ emp)) -∗
  (∀ m_snap,
    {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
        tbody c  @[ip_of_address sa] 
    {{{ (m_cache : gmap Key (option val * bool)), RET #();
        ⌜dom m_snap = dom m_cache⌝ ∗
        ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
          Q m_snap m_cache }}}) -∗
    (|={⊤, E}=> ∃ m_commit, ([∗ map] k ↦ vo ∈ m_commit, OwnMemKeyVal k vo) 
        ∗ ▷ (∀ m_cache m_snap, ⌜dom m_cache = dom m_snap = dom m_commit⌝ ∗
             (Q m_snap m_cache ∗
                ([∗ map] k↦ vo;p ∈ m_commit; m_cache, OwnMemKeyVal k (commitTxt p vo)) ={E, ⊤}=∗ R1 m_snap m_cache) ∧
              (([∗ map] k ↦ vo ∈ m_commit, OwnMemKeyVal k vo) ={E, ⊤}=∗ R2))) -∗
  {{{ ConnectionStateTxt c sa TxtCanStart }}}
        SI_run c tbody @[ip_of_address sa] E
  {{{ ∃ m_snap m_cacheb_ret, RET #b_ret;
      ConnectionStateTxt c sa TxtCanStart ∗ 
      if b_ret then R1 m_snap m_cache else R2 }}}.
Proof.
Admitted. *)

(* Lemma run_spec_derived_candidate_3 :
∀ (c : val) (tbody : val)
(m_cache : gmap Key (option val * bool))
(sa : socket_address) (E : coPset)
(P :  gmap Key (option val) → iProp Σ)
(Q :  gmap Key (option val * bool) → iProp Σ),
⌜↑KVS_InvName ⊆ E⌝ -∗
⌜start_spec⌝ -∗ 
⌜commit_spec⌝ -∗
IsConnected c sa -∗
□ (|={⊤, E}=> ∃ m_snap m_new, ⌜dom m_new = dom m_snap = dom m_cache⌝ ∗ P m_snap ∗ ([∗ map] k ↦ vo ∈ m_new, OwnMemKeyVal k vo)
  ∗ ▷ (((Q m_cache ∗ ([∗ map] k↦ vo;p ∈ m_new; m_cache, OwnMemKeyVal k (commitTxt p vo)))
        ∨ (([∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo))) ={E, ⊤}=∗ emp)) -∗
(∀ m_snap,
  {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
      tbody c  @[ip_of_address sa]
  {{{ RET #(); ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗ Q m_cache }}}) -∗
{{{ ConnectionStateTxt c sa TxtCanStart }}}
      SI_run c tbody @[ip_of_address sa] ⊤
{{{ b, RET #b; ConnectionStateTxt c sa TxtCanStart }}}.
Proof. *)


  (* This one is trying to be as simple as possible by doing two things:
  i) the two viewshifts are collected under the persistent modality 
  ii) no seen information in the postcondition *)
  Lemma run_spec_derived_candidate_3 :
    ∀ (c : val) (tbody : val)
    (m_cache : gmap Key (option val * bool))
    (sa : socket_address) (E : coPset)
    (P :  gmap Key (option val) → iProp Σ)
    (Q :  gmap Key (option val * bool) → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜start_spec⌝ -∗ 
    ⌜commit_spec⌝ -∗
    IsConnected c sa -∗
    □ (|={⊤, E}=> ∃ m_snap, ⌜dom m_snap = dom m_cache⌝ ∗ P m_snap ∗ ([∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo)
      ∗ ▷ (((Q m_cache ∗ ([∗ map] k↦ vo;p ∈ m_snap; m_cache, OwnMemKeyVal k (commitTxt p vo)))
            ∨ (([∗ map] k ↦ vo ∈ m_snap, OwnMemKeyVal k vo))) ={E, ⊤}=∗ emp)) -∗
    (∀ m_snap,
      {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
          tbody c  @[ip_of_address sa]
      {{{ RET #(); ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗ Q m_cache }}}) -∗
    {{{ ConnectionStateTxt c sa TxtCanStart }}}
          SI_run c tbody @[ip_of_address sa] ⊤
    {{{ b, RET #b; ConnectionStateTxt c sa TxtCanStart }}}.
  Proof.
    iIntros (c tbody m_cache sa E P Q H_sub H_start_spec H_commit_spec)
      "#H_conn #H_shift #H_body".
    iIntros (Φ) "!# H_state HΦ".
    rewrite /SI_run /= /run.
    wp_pures.
    wp_apply start_spec_derived; try eauto.
    iPoseProof "H_shift" as "H_shift'".
    iMod "H_shift'" as (m_snap_start) "(%H_dom & H_P & H_keys & H_shift')".
    iModIntro.
    iExists m_snap_start.
    iFrame.
    iModIntro.
    iIntros "(H_state & H_keys & H_cache)".
    iMod ("H_shift'" with "[$H_keys]") as "_".
    iModIntro.
    wp_pures.
    wp_apply ("H_body" $! m_snap_start  with "[$H_cache $H_P]"). 
    iIntros "(H_cache & H_Q)".
    wp_pures.
    wp_apply commit_spec_derived; try eauto.
    iMod "H_shift" as (m_snap_commit) "(%H_dom' & H_P & H_keys & H_shift)".
    iModIntro.
    iExists m_snap_commit, m_snap_start, m_cache.
    iFrame.
    iSplit.
    {
      iPureIntro.
      by rewrite H_dom H_dom'.
    }
    iModIntro.
    iIntros (b) "(H_state & [(-> & H_keys) | (-> & H_keys)])".
    - iMod ("H_shift" with "[H_keys H_Q]") as "_".
      + iLeft.
        iFrame.
      + iModIntro.
        by iApply "HΦ".
    - iMod ("H_shift" with "[H_keys]") as "_".
      + by iRight.
      + iModIntro.
        by iApply "HΦ".
  Qed.

End Specs.

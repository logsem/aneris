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

  Definition run' : val :=
  λ: "cst" "handler", start "cst";;
                      "handler" "cst";;
                       commit "cst".
  
  Lemma run_spec_derived :
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
           {{{ ([∗ map] k ↦ vo ∈ m_snap, k ↦{c} vo ∗
                 KeyUpdStatus c k false) ∗
               P m_snap }}}
           tbody c  @[ip_of_address sa] 
           {{{ (m_cache : gmap Key (option val * bool)), RET #();
               ⌜dom m_snap = dom m_cache⌝ ∗
               ([∗ map] k ↦ p ∈ m_cache, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
                Q m_snap m_cache }}})
      -∗
        □ (∀ m_curr, ConnectionStateTxt c sa (TxtActive m_curr) ∗
             ([∗ map] k↦vo ∈ m_curr, OwnMemKeyVal k vo)  ={E, ⊤}=∗
          |={⊤,E}=> (ConnectionStateTxt c sa (TxtActive m_curr) ∗
             ([∗ map] k ↦ vo ∈ m_curr, OwnMemKeyVal k vo))) -∗
    <<< ∀∀ m_curr, ConnectionStateTxt c sa TxtCanStart ∗
               P m_curr ∗
               [∗ map] k ↦ vo ∈ m_curr, OwnMemKeyVal k vo >>>
           SI_run c tbody @[ip_of_address sa] E
    <<<▷∃∃ mc b, RET #b;
        ConnectionStateTxt c sa TxtCanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ Q m_curr mc ∗
          ([∗ map] k↦ vo;p ∈ m_curr; mc, OwnMemKeyVal k (commitTxt p vo))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗
           [∗ map] k ↦ vo ∈ m_curr, OwnMemKeyVal k vo)) >>>.
  Proof.
    iIntros (c tbody sa E P Q HE HspecS HspecC).
    iIntros "#HiC #Hbody #pre_body".
    iIntros (Φ) "!# Hsh".
    rewrite /SI_run /= /run.
    wp_pures.
    wp_apply start_spec_derived; try eauto.
    iMod "Hsh".
    iDestruct "Hsh" as (m_curr) "((Hst & HP & Hks) & Hsh)".
    iModIntro.
    iExists m_curr.
    iFrame.
    iNext.
    iIntros "(Hst & Hks & Hcs)".
    iMod ("pre_body" $! m_curr with "[$Hst $Hks]") as "Hcl".
    iModIntro.
    wp_pures.
    wp_apply ("Hbody" $! m_curr  with "[$Hcs $HP]"). 
    iIntros (m_cache) "(%Hdom & Hcache)".
    wp_pures.
    wp_apply commit_spec_derived; try eauto.
   Admitted.
  
 End Specs.

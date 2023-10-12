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
  user_params time events aux_defs resource_algebras resources.

Set Default Proof Using "Type".

(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (vo : option val)
      (k : Key) (v : SerializableVal) (b : bool) ,
      ⌜k ∈ KVS_keys⌝ -∗
      IsConnected c sa -∗
    {{{ k ↦{c} vo ∗ KeyUpdStatus c k b}}}
      SI_write c #k v @[ip_of_address sa] 
    {{{ RET #(); k ↦{c} Some v.(SV_val) ∗ KeyUpdStatus c k true }}}.

  Definition read_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val),
    ⌜k ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗
    {{{ k ↦{c} vo }}}
      SI_read c #k @[ip_of_address sa] 
    {{{ RET $vo; k ↦{c} vo }}}.

   Definition start_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      IsConnected c sa -∗
    <<< ∀∀ (m : gmap Key Hist),
       ConnectionState c sa CanStart ∗
       [∗ map] k ↦ h ∈ m, k ↦ₖ h >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState c sa (Active m) ∗
       ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
       ([∗ map] k ↦ h ∈ m, k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗
       ([∗ map] k ↦ h ∈ m, Seen k h)>>>.

  Definition commit_spec : Prop :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
     ⌜↑KVS_InvName ⊆ E⌝ -∗
     IsConnected c sa -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc,
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, k ↦ₖ h ∗ Seen k h)) >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        KVS_ClientCanConnect sa ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionState cstate sa CanStart ∗
                            IsConnected cstate sa }}}.

  Definition init_kvs_spec : Prop :=
  {{{ KVS_address ⤇ KVS_si ∗
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address)
                   {[port_of_address KVS_address]} ∗
      KVS_Init }}}
      SI_init_server (s_serializer KVS_serialization)
        #KVS_address
        @[(ip_of_address KVS_address)]
    {{{ RET #(); True }}}.

  Lemma run_spec_derived_generic :
    ∀ (c : val) (tbody : val) (sa : socket_address) (E : coPset)
      (P :  gmap Key Hist → iProp Σ)
      (Q : (gmap Key Hist) -> (gmap Key (option val * bool)) → iProp Σ),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      ⌜start_spec⌝ -∗
      ⌜commit_spec⌝ -∗
      IsConnected c sa -∗
      □ (|={⊤, E}=>
         ∃ m_at_start, P m_at_start ∗ ([∗ map] k ↦ h ∈ m_at_start, k ↦ₖ h) ∗ 
            ▷ (([∗ map] k ↦ h ∈ m_at_start, k ↦ₖ h) ={E, ⊤}=∗
               (∀ mc,
                   |={⊤, E}=>                          
                   ∃ m_at_commit, (([∗ map] k ↦ h ∈ m_at_commit, k ↦ₖ h) ∗
                     ⌜dom m_at_commit = dom m_at_start⌝ ∗ ⌜dom m_at_start = dom mc⌝ ∗
                     (▷(([∗ map] k↦ h;p ∈ m_at_commit; mc,  k ↦ₖ (commit_event p h)) ∨
                        ([∗ map] k ↦ h ∈ m_at_commit, k ↦ₖ h))
                      ={E, ⊤}=∗ emp))))) -∗
   (∀ (m_snap : gmap Key Hist),
     {{{ ([∗ map] k ↦ h ∈ m_snap, k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
       tbody c  @[ip_of_address sa] 
     {{{ (mc : gmap Key (option val * bool)), RET #();
        ⌜dom m_snap = dom mc⌝ ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
        Q m_snap mc }}}) -∗
     {{{ ConnectionState c sa CanStart }}}
       (λ: "cst" "handler", SI_start "cst";; "handler" "cst";; SI_commit "cst")%V
          c tbody @[ip_of_address sa] 
     {{{ m ms mc (b : bool), RET #b;
         ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
         ([∗ map] k↦ h;p ∈  m; mc, Seen k (commit_event p h)) ∗ Q ms mc) ∨
        (** Transaction has been aborted. *)
          (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗ [∗ map] k ↦ h ∈ m, Seen k h)) }}}.
  Proof.
    iIntros (c bdy sa E P Q HE) "%HspecS %HspecC #HiC #Hsh1 #HspecBdy !# %Φ HstS HΦ". 
    wp_pures. wp_apply HspecS; try eauto.
    iMod "Hsh1" as (m_at_start) "(HP & Hks & Hsh1)".
    iModIntro. iExists m_at_start. iFrame.
    iNext. iIntros "(HstA & Hmks & Hcks & #Hseens1)".
    iMod ("Hsh1" with "[$Hmks]") as "Hsh2".
    iModIntro. wp_pures. wp_apply ("HspecBdy" with "[$HP $Hcks]").
    iIntros (mc) "(%Hdeq1 & Hcks & HQ)".
    wp_pures.  wp_apply HspecC; try eauto.
    iMod ("Hsh2" $! mc) as (m_at_commit) "(Hks & %Hdom1 & %Hdom2 & Hp)".
    iModIntro. iExists _, _, _. iFrame.
    iSplit; [iPureIntro; set_solver|].
    - iNext. iIntros (b) "(HstS & Hdisj)".
      iApply ("HΦ" $! m_at_commit m_at_start mc).
      iFrame. iDestruct "Hdisj" as "[Hc | Ha]".
      -- iDestruct "Hc" as "(%Hbt & %Hcm & Hkts)".
         rewrite big_sepM2_sep. iDestruct "Hkts" as "(Hkts & #Hseens2)".
         iMod ("Hp" with "[$Hkts]") as "_". iModIntro; iLeft; iFrame "#"; eauto.
      -- iDestruct "Ha" as "(%Hbf & %Hcmn & Hkts)".
         rewrite big_sepM_sep. iDestruct "Hkts" as "(Hkts & #Hseens2)".
         iMod ("Hp" with "[$Hkts]") as "_". iModIntro; iRight; iFrame; eauto.
  Qed.


(*    Lemma run_spec_derived_generic :
    ∀ (c : val) (tbody : val)
    (sa : socket_address) (E : coPset)
    (Q : (gmap Key Hist) -> (gmap Key (option val * bool)) → iProp Σ)
    (P :  gmap Key Hist → iProp Σ),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      ⌜start_spec⌝ -∗ 
      ⌜commit_spec⌝ -∗
      IsConnected c sa -∗
      □ (|={⊤, E}=>
         (* State after transaction has started, before body is executed. *)
         ∃ m_at_start,
            P m_at_start ∗
            ([∗ map] k ↦ h ∈ m_at_start, k ↦ₖ h) ∗ 
            ▷ (([∗ map] k ↦ h ∈ m_at_start, k ↦ₖ h)  ={E, ⊤}=∗
               emp)) -∗
      (* State after the body has been executed, before committing the transaction. *)
      □ (∀ (m_at_start : gmap Key Hist) mc,
          |={⊤, E}=>                          
             ∃ m_at_commit,
               (([∗ map] k ↦ h ∈ m_at_commit, k ↦ₖ h) ∗
                 ⌜dom m_at_commit = dom m_at_start⌝ ∗
                 ⌜dom m_at_start = dom mc⌝ ∗
                 (▷(([∗ map] k↦ h;p ∈ m_at_commit; mc,  k ↦ₖ (commit_event p h)) ∨
                   ([∗ map] k ↦ h ∈ m_at_commit, k ↦ₖ h))={E, ⊤}=∗
                    emp))) -∗
   (* Specification for the execution of the transaction's body. *)
   (∀ (m_snap : gmap Key Hist),
     {{{ ([∗ map] k ↦ h ∈ m_snap, k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗ P m_snap }}}
       tbody c  @[ip_of_address sa] 
     {{{ (mc : gmap Key (option val * bool)), RET #();
        ⌜dom m_snap = dom mc⌝ ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗
        Q m_snap mc }}}) -∗
   (* Specification for the transaction execution. *)
     {{{ ConnectionState c sa CanStart }}}
       (λ: "cst" "handler", SI_start "cst";; "handler" "cst";; SI_commit "cst")%V
          c tbody @[ip_of_address sa] 
     {{{ m_commit m_snap mc (b : bool), RET #b;
         ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m_commit m_snap mc⌝ ∗
         ([∗ map] k↦ h;p ∈  m_commit; mc, Seen k (commit_event p h)) ∗
         Q m_snap mc) ∨
        (** Transaction has been aborted. *)
          (⌜b = false⌝ ∗ ⌜¬ can_commit m_commit m_snap mc⌝ ∗
                  [∗ map] k ↦ h ∈ m_commit, Seen k h)) }}}.
  Proof.
    iIntros (c bdy sa E Q P HE).
    iIntros "%HspecS %HspecC #HiC #Hsh1 #Hsh2 #HspecBdy".
    iIntros "!# %Φ HstS HΦ". 
    wp_pures.
    wp_apply HspecS; try eauto.
    iMod "Hsh1" as (m_at_start) "(HP & Hks & Hsh1)".
    iModIntro.
    iExists m_at_start.
    iFrame.
    iNext.
    iIntros "(HstA & Hmks & Hcks & #Hseens1)".
    iMod ("Hsh1" with "[$Hmks]") as "_".
    iModIntro.
    wp_pures.
    wp_apply ("HspecBdy" with "[$HP $Hcks]").
    iIntros (mc) "(%Hdeq1 & Hcks & HQ)".
    wp_pures.
    wp_apply HspecC; try eauto.
    iMod ("Hsh2" $! m_at_start mc) as (m_at_commit) "(Hks & %Hdom1 & %Hdom2 & Hp)".
    iModIntro.
    iExists _, _, _.
    iFrame.
    iSplit.
    - iPureIntro. set_solver.
    - iNext.
      iIntros (b) "(HstS & Hdisj)".
      iApply ("HΦ" $! m_at_commit m_at_start mc).
      iFrame.
      iDestruct "Hdisj" as "[Hc | Ha]".
      -- iDestruct "Hc" as "(%Hbt & %Hcm & Hkts)".
         rewrite big_sepM2_sep.
         iDestruct "Hkts" as "(Hkts & #Hseens2)".
         iMod ("Hp" with "[$Hkts]") as "_".
         iModIntro.
         iLeft.
         iFrame "#∗"; eauto.
      -- iDestruct "Ha" as "(%Hbf & %Hcmn & Hkts)".
         rewrite big_sepM_sep.
         iDestruct "Hkts" as "(Hkts & #Hseens2)".
         iMod ("Hp" with "[$Hkts]") as "_".
         iModIntro.
         iRight.
         iFrame; eauto.
  Qed.*)
  
End Specification.

Canonical Structure valO := leibnizO val.

Notation KVSG Σ := (IDBG Σ).
 
Definition KVSΣ : gFunctors :=
  #[
      ghost_mapΣ Key (list write_eventO);
      ghost_mapΣ Key (option val * bool);
      GFunctor (authR (gmapUR Key (max_prefix_listR
                                     write_eventO)));
      GFunctor ((authR (gen_heapUR Key val)));
      GFunctor (authR (gmapUR nat (agreeR (gmapUR Key (max_prefix_listR write_eventO)))));
      GFunctor
        (authR (gmapUR socket_address (agreeR (leibnizO gname))));
      GFunctor ((csumR
                   (exclR unitR)
                   (agreeR ((gnameO * gnameO * gnameO * gnameO * gnameO) : Type))));
     GFunctor (exclR unitO);
     GFunctor (authUR (gsetUR nat));
     mono_natΣ;
     ras.SpecChanΣ;
     lockΣ].

Instance subG_KVSΣ {Σ} : subG KVSΣ Σ → KVSG Σ.
Proof. econstructor; solve_inG. Qed.

Section SI_Module.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVSG Σ, !KVS_snapshot_isolation_api}.

  Class SI_client_toolbox `{!SI_resources Mdl Σ} := {
    SI_init_kvs_spec : init_kvs_spec ;
    SI_init_client_proxy_spec : init_client_proxy_spec;
    SI_read_spec : read_spec ;
    SI_write_spec : write_spec;
    SI_start_spec : start_spec;
    SI_commit_spec : commit_spec;
  }.
 
   Class SI_init := {
    SI_init_module E (clients : gset socket_address) :
      ↑KVS_InvName ⊆ E →
       ⊢ |={E}=>
      ∃ (res : SI_resources Mdl Σ),
        ([∗ set] k ∈ KVS_keys, k ↦ₖ []) ∗
        KVS_Init ∗
        GlobalInv ∗
        ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa) ∗
        ⌜init_kvs_spec⌝ ∗
        ⌜init_client_proxy_spec⌝ ∗
        ⌜read_spec⌝ ∗
        ⌜write_spec⌝ ∗
        ⌜start_spec⌝ ∗
        ⌜commit_spec⌝
     }.
   
End SI_Module.
 

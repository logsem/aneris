From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.examples.reliable_communication.lib.repdb.resources Require Import log_resources.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library aux_defs.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs state_based_model implication_trace_util.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  (** Definitons and lemmas for the wrapped resources *)

  Inductive ind_rel_exec_map (k : Key) : execution → list val → Prop :=
  | Rel_exec_map_base : ind_rel_exec_map k [([], ∅)] []
  | Rel_exec_map_app1 exec s t h v :
     exec ≠ [] →
     (∃ sig v', Wr sig k v' ∈ t) →
     ind_rel_exec_map k exec h →
     ind_rel_exec_map k (exec ++ [(t, s)]) (h ++ [v])
  | Rel_exec_map_app2 exec s t h :
    exec ≠ [] →
    (¬ ∃ sig v, Wr sig k v ∈ t) →
    ind_rel_exec_map k exec h →
    ind_rel_exec_map k (exec ++ [(t, s)]) h.

  Definition rel_exec_map (exec : execution) (m : gmap Key (list val)) :=
    ∃ s, last (split exec).2 = Some s ∧
      (∀ k ov, k ∈ KVS_keys → (s !! k = ov ↔ (∃ h, m !! k = Some h ∧ last h = ov))) ∧
      (∀ k h, m !! k = Some h → ind_rel_exec_map k exec h).

  Definition reads_from_last_state (exec : execution) (k : Key) (ov : option val) := 
    ∃ s, last (split exec).2 = Some s ∧ s !! k = ov.

  Definition OwnExec (γ : gname) (exec : execution) : iProp Σ := own_log_auth γ 1%Qp exec.

  Definition OwnExecHist (γ : gname) (exec : execution) : iProp Σ := own_log_obs γ exec.

  Definition local_key_state (γsi_name γl : gname) (sa : socket_address) (c : val) (k : Key) (ov ov_last_wr : option val) : iProp Σ := 
    ∃ (γm_conn γsnap : gname), ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)) ∗
      ((⌜ov_last_wr = None⌝ ∗ ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov) ∨ 
      (∃ v, ⌜ov_last_wr = Some v ∧ ov = ov_last_wr⌝ ∗ ghost_map_elem γsnap k (DfracOwn 1%Qp) None)).

  Definition inactive_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) 
  (γmstate γm_conn γsnap : gname) (m_conn : gmap Key (option val)) : iProp Σ := 
    ⌜s = aux_defs.CanStart⌝ ∗
    ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, Some c) ∗
    ([∗ set] k ∈ KVS_keys, ∃ (ov : option val), (ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov ∨ ⌜m_conn !! k = None⌝) ∗
      ghost_map_elem γsnap k (DfracOwn 1%Qp) None).

  Definition active_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) (γexec γmstate γm_conn γsnap : gname) 
  (m_conn : gmap Key (option val)) : iProp Σ := 
    ∃ (ms ms_sub: gmap Key (list val)), ⌜s = aux_defs.Active ms_sub⌝ ∗ 
      ⌜∀ k (ov : option val), k ∈ KVS_keys → k ∈ dom (ms_sub) → (m_conn !! k = Some ov → (∃ h, ms_sub !! k = Some h ∧ last h = ov))⌝ ∗ 
      ∃ exec_pre, OwnExecHist γexec exec_pre ∗ ⌜rel_exec_map exec_pre ms ∧ ms_sub ⊆ ms⌝ ∗
        ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.Active (dom ms_sub), Some c) ∗
        ([∗ set] k ∈ KVS_keys ∖ (dom ms_sub ∩ KVS_keys), ⌜m_conn !! k = None⌝ ∗ ghost_map_elem γsnap k (DfracOwn 1%Qp) None).

  Definition connection_exec_state (s : aux_defs.local_state) (sa : socket_address) (c : val) (γexec γmstate γm_conn γsnap : gname) 
  (m_conn : gmap Key (option val)) : iProp Σ := 
    inactive_connection_exec_state s c sa γmstate γm_conn γsnap m_conn ∨ active_connection_exec_state s c sa γexec γmstate γm_conn γsnap m_conn.

  Definition open_transactions_state (T : list transaction) (mnames : gmap socket_address (option (gname * gname * val))) 
  (extract : val → option val) (clients : gset socket_address): iProp Σ := 
     ([∗ set] (sa : socket_address) ∈ clients, (⌜mnames !! sa = Some None⌝) ∨
      (∃ c (m_conn : gmap Key (option val)) (γm_conn γsnap : gname), 
        ⌜extract c = Some #sa ∧ mnames !! sa = Some (Some (γm_conn, γsnap, c))⌝ ∗
        ghost_map_auth γm_conn (1 / 2) m_conn ∗
        ∀ trans, ⌜(open_trans trans c T) → 
          ((∀ sig k ov v, ((Rd sig k ov) ∈ trans ∨ Wr sig k v ∈ trans) → k ∈ KVS_keys) ∧
           (∀ sig k ov, (Rd sig k ov) ∈ trans → 
            ¬ (∃ sig' v', rel_list trans (Wr sig' k v') (Rd sig k ov)) → m_conn !! k = Some ov))⌝)).

  Definition GlobalInvExtSI (γm_gl γexec γsi_name : gname) (T : list transaction) (exec : execution)
  (extract : val → option val) (clients : gset socket_address) : iProp Σ := 
    ∃ (mnames : gmap socket_address (option (gname * gname * val))), ghost_map_auth γsi_name (1%Qp) mnames ∗ 
    ∃ (m_gl : gmap Key (list val)), ghost_map_auth γm_gl (1%Qp) m_gl ∗ ⌜∀ k, k ∈ KVS_keys → is_Some (m_gl !! k)⌝ ∗
    OwnExec γexec exec ∗ ⌜rel_exec_map exec m_gl⌝ ∗
    open_transactions_state T mnames extract clients.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources (γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name : gname) (clients : gset socket_address)
  `(res : !SI_resources Mdl Σ) : SI_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_si ∗ 
                    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                    GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec))%I;
      OwnMemKey k h := (OwnMemKey k h ∗ ghost_map_elem γm_gl k (DfracOwn 1%Qp) h ∗
                        (∀ v, ⌜v ∈ h⌝ → ∃ lh tag c, OwnLinHist γl lh ∗
                          ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗  ∃ (sa : socket_address) γ ov_last_wr, ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                             ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov_last_wr) ∗ ⌜sa ∈ clients⌝ ∗ 
                             (∀ v, ⌜ov = Some v⌝ → ∃ lh tag c', OwnLinHist γl lh ∗ 
                              ⌜(#(LitString tag), (c', (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝) ∗
                             (⌜k ∈ KVS_keys⌝ → local_key_state γsi_name γl sa c k ov ov_last_wr))%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ 
                                 ∃ (γm_conn γsnap : gname) (m_conn : gmap Key (option val)), ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)) ∗
                                   ghost_map_auth γm_conn (1 / 2) m_conn ∗ connection_exec_state s sa c γexec γmstate γm_conn γsnap m_conn)%I;
      IsConnected c sa := (IsConnected c sa ∗ ⌜sa ∈ clients⌝ ∗ ⌜extract c = Some #sa⌝ ∗ 
                           ∃ (γ : gname), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                           ∃ (γm_conn γsnap : gname), ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)))%I;
      KVS_si := KVS_si;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ 
                                  ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, None) ∗ ⌜sa ∈ clients⌝ ∗
                                  ghost_map_elem γsi_name sa (DfracOwn 1%Qp) (None : option (gname * gname * val)))%I;
      KeyUpdStatus c k b := (KeyUpdStatus c k b ∗ ∃ (sa : socket_address) (γm_conn γsnap : gname), ⌜extract c = Some #sa⌝ ∗
                              ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)) ∗ 
                              (⌜k ∈ KVS_keys⌝ → ((⌜b = true⌝ ∧ ∃ (ov : option val), ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov) ∨ 
                                (⌜b = false⌝ ∧ ghost_map_elem γsnap k (DfracOwn 1%Qp) None))))%I;
      Seen k V := Seen k V%I;
      extract c := res.(snapshot_isolation.specs.resources.extract) c;
    |}.
  Next Obligation.
    iIntros (?????????????) "(Hkey & [%sa [%γ [%ov' (Hghost_elem_per & %Hextract & Hghost_elem & Hstate)]]])".
    iDestruct (res.(snapshot_isolation.specs.resources.OwnLocalKey_serializable) 
      with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iExists sa, γ, ov'.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (??????????????).
    iIntros (?) "#(HGinv & Hinv) (#Hseen & Hkey & Hin)".
    iMod (res.(snapshot_isolation.specs.resources.Seen_valid) 
      with "[$HGinv][$Hseen $Hkey]") as "(Hkey & Hsub)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (??????????????) "#(HGinv & Hinv) (Hkey & Hin)".
    iMod (res.(snapshot_isolation.specs.resources.Seen_creation) 
      with "[$HGinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????? clients res sa c) "(Hconn & _)".
    iApply (res.(snapshot_isolation.specs.resources.Extraction_of_address) 
      with "[$Hconn]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????).
    iIntros (clients res sa sa' c c' Heq1 Heq2 Hneq).
    by eapply res.(snapshot_isolation.specs.resources.Extraction_preservation).
  Qed.

  (** Helper lemmas *)

  Lemma rel_exec_map_init :
    rel_exec_map [([], ∅)] (gset_to_gmap [] KVS_keys).
  Proof.
    exists ∅.
    split_and!.
    - by simpl.
    - intros k ov Hk_in.
      rewrite lookup_empty.
      split.
      + intros <-.
        exists [].
        rewrite lookup_gset_to_gmap_Some.
        simpl.
        set_solver.
      + intros (h & Hmap & Hlast).
        rewrite lookup_gset_to_gmap_Some in Hmap.
        subst.
        destruct Hmap as (_ & <-).
        by simpl.
    - intros k h Hlookup.
      rewrite lookup_gset_to_gmap_Some in Hlookup.
      destruct Hlookup as (_ & <-). 
      apply Rel_exec_map_base.
  Qed.

  Lemma rev_exists {A : Type} (l : list A) :
    ∃ l', l = rev l'.
  Proof.
    exists (rev l).
    by rewrite rev_involutive.
  Qed.

  Lemma rel_exec_prefix k exec1 exec2 :
    exec1 !! 0 = Some ([], ∅) →
    ∀ h, ind_rel_exec_map k (exec1 ++ exec2) h →
    ∃ h', ind_rel_exec_map k exec1 h' ∧ length h' ≤ length h.
  Proof.
    destruct (rev_exists exec2) as (exec2' & ->).
    generalize dependent exec1.
    induction exec2' as [|e exec2' IH].
    - intros exec1 Hlookup h Hrel. 
      exists h.
      split; last lia.
      simpl in Hrel.
      by rewrite app_nil_r in Hrel.
    - intros exec1 Hlookup h Hrel.
      simpl in Hrel.
      inversion Hrel as [Heq1 Heq2 | exec s t h' v Hneq Hwr Hrel' Heq1 Heq2| 
        exec s t h' Hneq Hnot Hrel' Heq1 Heq2].
      + rewrite -(app_nil_l [([], ∅)]) in Heq1.
        rewrite app_assoc in Heq1.
        apply app_inj_tail in Heq1.
        destruct Heq1 as (Heq1 & _).
        apply eq_sym in Heq1.
        apply app_eq_nil in Heq1.
        destruct Heq1 as (Heq1 & _).
        by rewrite Heq1 lookup_nil in Hlookup.
      + rewrite app_assoc in Heq1.
        apply app_inj_tail in Heq1.
        destruct Heq1 as (Heq1 & _).
        rewrite Heq1 in Hrel'.
        destruct (IH exec1 Hlookup h' Hrel') as (h'' & Hrel'' & Hlength).
        exists h''.
        split; first done.
        rewrite last_length.
        lia.
      + rewrite app_assoc in Heq1.
        apply app_inj_tail in Heq1.
        destruct Heq1 as (Heq1 & _).
        rewrite Heq1 in Hrel'.
        destruct (IH exec1 Hlookup h Hrel') as (h'' & Hrel'' & Hlength).
        exists h''.
        split; first done.
        lia.
  Qed.

  Lemma rel_exec_prefix_length_not k h1 h2 exec : 
    exec !! 0 = Some ([], ∅) →
    ind_rel_exec_map k exec h1 →
    ind_rel_exec_map k exec h2 →
    length h1 < length h2 →
    false.
  Proof.
    generalize dependent h1.
    generalize dependent h2.
    destruct (rev_exists exec) as (exec' & ->).
    induction exec' as [|e exec' IH]; intros h2 h1 Hzero Hrel1 Hrel2 Hlt; simpl in Hrel1.
    - inversion Hrel1; destruct exec; set_solver.
    - simpl in Hrel2.
      assert (rev (exec') !! 0 = Some ([], ∅)) as Hzero'.
      {
        simpl in Hzero.
        rewrite lookup_app_Some in Hzero.
        destruct Hzero as [Hzero | Hzero]; first done.
        destruct (length (rev exec')) as [| n] eqn:Hlength; rewrite Hlength in Hzero; last lia.
        apply nil_length_inv in Hlength.
        rewrite Hlength in Hrel1, Hrel2.
        simpl in Hrel1, Hrel2.
        inversion Hrel1 as [Heq1 Heq2 | exec1 s t h1_less v Hwr Hneq Hrel Heq1 Heq2 | 
          exec1 s t h1_less Hneq Hnot Hrel Heq1 Heq2].
        2, 3 : destruct exec1 as [|e' exec1]; first set_solver.
        2, 3 : rewrite -(app_nil_l [e]) in Heq1.
        2, 3 : apply app_inj_tail in Heq1; set_solver.
        inversion Hrel2 as [Heq1' Heq2' | exec2 s' t' h2_less v' Hneq' Hwr' Hrel' Heq1' Heq2' | 
          exec2 s' t' h1_less' Hneq' Hnot' Hrel' Heq1' Heq2'].
        2, 3 : destruct exec2 as [|e' exec2]; first set_solver.
        2, 3 : rewrite -(app_nil_l [e]) in Heq1'.
        2, 3 : apply app_inj_tail in Heq1'; set_solver.
        rewrite -Heq2 -Heq2' in Hlt.
        simpl in Hlt.
        lia.
      }
      inversion Hrel1 as [Heq1 Heq2 | exec1 s t h1_less v Hwr Hneq Hrel Heq1 Heq2 | 
        exec s t h1_less Hneq Hnot Hrel Heq1 Heq2].
      + rewrite -(app_nil_l [([], ∅)]) in Heq1.
        apply app_inj_tail in Heq1.
        destruct Heq1 as (Heq1 & _).
        rewrite -Heq1 in Hzero'.
        by rewrite lookup_nil in Hzero'.
      + inversion Hrel2 as [Heq1' Heq2' | exec2 s' t' h2_less v' Hneq' Hwr' Hrel' Heq1' Heq2' | 
          exec2 s' t' h1_less' Hneq' Hnot' Hrel' Heq1' Heq2'].
        * rewrite -(app_nil_l [([], ∅)]) in Heq1'.
          apply app_inj_tail in Heq1'.
          destruct Heq1' as (Heq1' & _).
          rewrite -Heq1' in Hzero'.
          by rewrite lookup_nil in Hzero'.
        * apply app_inj_tail in Heq1; destruct Heq1 as (Heq1 & _).
          apply app_inj_tail in Heq1'; destruct Heq1' as (Heq1' & _).
          rewrite Heq1 in Hrel.
          rewrite Heq1' in Hrel'.
          apply (IH h2_less h1_less); try done.
          rewrite -Heq2 -Heq2' in Hlt.
          do 2 rewrite app_length in Hlt.
          simpl in Hlt.
          lia.
        * apply Hnot'.
          assert (t' = t) as ->; last set_solver.
          apply app_inj_tail in Heq1.
          apply app_inj_tail in Heq1'.
          set_solver.
      + inversion Hrel2 as [Heq1' Heq2' | exec2 s' t' h2_less v' Hneq' Hwr' Hrel' Heq1' Heq2' | 
          exec2 s' t' h1_less' Hneq' Hnot' Hrel' Heq1' Heq2'].
        * rewrite -(app_nil_l [([], ∅)]) in Heq1'.
          apply app_inj_tail in Heq1'.
          destruct Heq1' as (Heq1' & _).
          rewrite -Heq1' in Hzero'.
          by rewrite lookup_nil in Hzero'.
        * apply Hnot.
          assert (t' = t) as ->; last set_solver.
          apply app_inj_tail in Heq1.
          apply app_inj_tail in Heq1'.
          set_solver.
        * apply app_inj_tail in Heq1; destruct Heq1 as (Heq1 & _).
          apply app_inj_tail in Heq1'; destruct Heq1' as (Heq1' & _).
          rewrite Heq1 in Hrel.
          rewrite Heq1' in Hrel'.
          apply (IH h2 h1); try done.
  Qed.

  Lemma rel_exec_prefix_write_not k h exec1 exec2 :
    exec1 !! 0 = Some ([], ∅) →
    ind_rel_exec_map k exec1 h →
    ind_rel_exec_map k (exec1 ++ exec2) h →
    ¬∃ t sig v, t ∈ (split exec2).1 ∧ Wr sig k v ∈ t.
  Proof.
    intros Hzero Hrel1 Hrel2 (t & s & sig & Ht_in & Hwr_in).
    rewrite elem_of_list_lookup in Ht_in.
    destruct Ht_in as (i & Hlookup).
    destruct (exec2 !! i) as [(t', s')|] eqn:Hlookup'.
    - assert (t' = t) as <-; first by eapply split_lookup_eq. 
      assert ((t', s') ∈ exec2) as Hin.
      {
        apply elem_of_list_lookup.
        eauto.
      }
      apply elem_of_list_split in Hin.
      destruct Hin as (l1 & l2 & Heq).
      rewrite Heq app_assoc cons_middle app_assoc in Hrel2.
      assert (((exec1 ++ l1) ++ [(t', s')]) !! 0 = Some ([], ∅)) as Hzero'; 
        first by do 2 (apply lookup_app_Some; left).
      destruct (rel_exec_prefix k ((exec1 ++ l1) ++ [(t', s')]) l2 Hzero' h Hrel2) as (h' & Hrel_less & Hlength).
      inversion Hrel_less as [Heq1 Heq2 | exec s'' t h'' v Hneq Hwr Hrel' Heq1 Heq2| 
        exec s'' t h'' Hneq Hnot Hrel' Heq1 Heq2].
      + rewrite -(app_nil_l [([], ∅)]) in Heq1.
        apply app_inj_tail in Heq1.
        destruct Heq1 as (Heq1 & _).
        apply eq_sym in Heq1.
        apply app_eq_nil in Heq1.
        destruct Heq1 as (Heq1 & _).
        by rewrite Heq1 lookup_nil in Hzero.
      + apply app_inj_tail in Heq1. 
        destruct Heq1 as (Heq1 & _).
        rewrite Heq1 in Hrel'.
        destruct (rel_exec_prefix k exec1 l1 Hzero h'' Hrel') as (h''' & Hrel_less' & Hlength').
        assert (length h''' < length h) as Hlt.
        {
          eapply (Nat.le_lt_trans _ (length h'')); try done.
          eapply (Nat.lt_le_trans _ (length h')); try done.
          rewrite -Heq2.
          rewrite app_length.
          simpl.
          lia.
        }
        by apply (rel_exec_prefix_length_not k h''' h exec1).
      + apply Hnot.
        apply app_inj_tail in Heq1.
        set_solver.
    - apply lookup_ge_None_1 in Hlookup'.
      rewrite -split_length_l in Hlookup'.
      apply lookup_ge_None_2 in Hlookup'.
      set_solver.
  Qed.

  Lemma prefix_exists {A : Type} (l1 l2 : list A): 
    l1 `prefix_of` l2 →
    ∃ l3, l2 = l1 ++ l3.
  Proof.
    generalize dependent l2.
    destruct (rev_exists l1) as (l1' & ->).
    induction l1' as [|h l1' IH]; first set_solver.
    intros l2 Hprefix.
    simpl.
    simpl in Hprefix.
    pose proof Hprefix as Hprefix'. 
    apply prefix_app_l in Hprefix.
    destruct (IH l2 Hprefix) as (l3 & Heq).
    rewrite Heq.
    destruct l3 as [|h' l3].
    - rewrite app_nil_r in Heq.
      rewrite -Heq in Hprefix'.
      exfalso.
      by eapply prefix_snoc_not.
    - exists l3.
      assert (h = h') as ->.
      + rewrite Heq in Hprefix'.
        apply prefix_app_inv in Hprefix'.
        by apply prefix_cons_inv_1 in Hprefix'.
      + rewrite -app_assoc. 
        apply cons_middle.
  Qed.

  Lemma valid_execution_si_imp exec_pre m_pre exec m s st trans T :
    rel_exec_map exec_pre m_pre →
    rel_exec_map exec m →
    exec_pre `prefix_of` exec →
    (∀ s k v, Wr s k v ∈ trans → ∃ h, m_pre !! k = Some h ∧ m !! k = Some h) →
    optional_applied_transaction exec st (trans ++ [Cm s true]) →
    based_on exec T →
    (trans ++ [Cm s true]) ∉ T →
    (∀ s k ov, Rd s k ov ∈ trans → 
      (¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k ov))) → 
      reads_from_last_state exec_pre k ov) →
    valid_execution commit_test_si exec →
    valid_execution commit_test_si (exec ++ [((trans ++ [Cm s true]), st)]).
  Proof.
    intros Hrel_ex Hrel_ex' Hpre Hwrites Happl Hbased Hnin Hreads Hvalid.
    split_and!.
    - destruct Happl as [(s' & t' & Hlast & Happl)|Hfalse].
      + intros i eq e2. 
        eapply extend_execution_imp; try done.
      + rewrite /valid_execution in Hvalid.
        rewrite last_None in Hfalse.
        set_solver.
    - destruct Hvalid as (_ & Hvalid & _).
      rewrite lookup_app_Some.
      set_solver.
    - intros t Hin.
      rewrite split_split in Hin.
      simpl in Hin.
      rewrite elem_of_app in Hin.
      pose proof Hvalid as Hvalid'.
      destruct Hvalid as (_ & _ & Hvalid & _).
      destruct Hin as [Hin|Hin].
      + destruct (Hvalid t Hin) as (s' & i_s' & Hin_s' & Hcompl & Hno_conf).
        exists s', i_s'.
        split_and!.
        * rewrite split_split.
          simpl.
          rewrite lookup_app_Some.
          by left.
        * intros tag c k ov i Hlookup_i Hrd_in Hno_write.
          assert ((split exec).1 !! i = Some t) as Ht_in.
          {
            rewrite split_split in Hlookup_i.
            simpl in Hlookup_i.
            rewrite lookup_app_Some in Hlookup_i.
            destruct Hlookup_i as [Hlookup_i|Hlookup_i]; first done.
            exfalso.
            apply Hnin.
            rewrite list_lookup_singleton_Some in Hlookup_i.
            destruct Hlookup_i as (_ & _ & Hlookup_i).
            rewrite Hlookup_i.
            apply (Hbased t).
            split; first done.
            rewrite -Hlookup_i; intros Hfalse. 
            destruct trans; set_solver.
          }
          rewrite /complete in Hcompl.
          by apply (Hcompl tag c k ov i).
        * intros i' j t' Hlookup_i' Hlookup_j Hlt.
          eapply (Hno_conf i' j); try done.
          -- rewrite split_split in Hlookup_i'.
             simpl in Hlookup_i'.
             rewrite lookup_app_Some in Hlookup_i'.
             destruct Hlookup_i' as [Hlookup_i'|Hlookup_i']; first done.
             exfalso.
             rewrite split_split in Hlookup_j.
             simpl in Hlookup_j.
             rewrite lookup_app_Some in Hlookup_j.
             destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)].
             ++ apply lookup_lt_Some in Hlookup_j.
                lia.
             ++ rewrite list_lookup_singleton_Some Nat.sub_0_le in Hlookup_j.
                lia.
          -- rewrite split_split in Hlookup_j.
             simpl in Hlookup_j.
             rewrite lookup_app_Some in Hlookup_j.
             destruct Hlookup_j as [Hlookup_j|Hlookup_j]; first done.
             exfalso.
             apply Hnin.
             rewrite list_lookup_singleton_Some in Hlookup_j.
             destruct Hlookup_j as (_ & _ & Hlookup_j).
             rewrite Hlookup_j.
             apply (Hbased t).
             split; first done.
             rewrite -Hlookup_j; intros Hfalse. 
             destruct trans; set_solver.
      + assert (t = trans ++ [Cm s true]) as ->; first set_solver.
        destruct Hrel_ex as (s_snap & Hrel_ex).
        exists s_snap, (Init.Nat.pred (length exec_pre)).
        assert ((split exec_pre).2 !! (Init.Nat.pred (length exec_pre)) = Some s_snap) as Hsnap_lookup.
        {
          rewrite -split_length_r.
          rewrite -last_lookup.
          set_solver.
        }
        apply prefix_exists in Hpre.
        destruct Hpre as (exec' & Heq_pre).
        split_and!.
        * rewrite split_split. 
          simpl.
          subst.
          rewrite lookup_app_Some.
          left.
          rewrite split_split.
          simpl.
          rewrite lookup_app_Some.
          by left.
        * intros tag c key ov i Hlookup_i Hrd_in Hno_writes.
          rewrite /read_state.
          rewrite split_split in Hlookup_i.
          simpl in Hlookup_i.
          rewrite lookup_app_Some in Hlookup_i.
          destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
          -- exfalso.
             apply Hnin.
             apply (Hbased (trans ++ [Cm s true])).
             split; first (apply elem_of_list_lookup; eauto).
             intros Hfalse. 
             destruct trans; set_solver.
          -- split_and!.
             ++ rewrite Heq_pre in Hlength_i.
                rewrite split_length_l in Hlength_i.
                rewrite app_length in Hlength_i.
                assert (length exec_pre ≤ i) as Hleq; first lia.
                destruct (length exec_pre) eqn:Heq_length; last lia.
                rewrite -split_length_r in Heq_length.
                apply nil_length_inv in Heq_length.
                rewrite Heq_length in Hsnap_lookup.
                by simpl in Hsnap_lookup.
             ++ rewrite elem_of_app in Hrd_in.
                destruct Hrd_in as [Hrd_in|Hrd_in]; last set_solver.
                assert (reads_from_last_state exec_pre key ov) as (s_snap' & Heq & Hlookup); last set_solver.
                apply (Hreads (tag, c) key ov Hrd_in).
                intros (s' & v' & Hrel).
                apply Hno_writes.
                exists s', v'.
                by apply rel_list_imp.
        * intros i' j t' Hlookup_i' Hlookup_j Hlt k (s' & v & Hwr_in) Hwr_in'.
          rewrite elem_of_app in Hwr_in.
          destruct Hwr_in as [Hwr_in|Hwr_in]; last set_solver.
          destruct (Hwrites s' k v Hwr_in) as (h & Hlookup_k & Hlookup_k').
          apply (rel_exec_prefix_write_not k h exec_pre exec').
          -- destruct Hvalid' as (_ & Hzero & _).
             rewrite Heq_pre in Hzero.
             rewrite lookup_app_Some in Hzero.
             destruct Hzero as [Hzero | Hzero]; first done.
             destruct (length exec_pre) as [| n] eqn:Hlength; rewrite Hlength in Hzero; last lia.
             apply nil_length_inv in Hlength.
             rewrite Hlength in Hrel_ex.
             simpl in Hrel_ex.
             set_solver.
          -- set_solver.
          -- rewrite Heq_pre /rel_exec_map in Hrel_ex'.
             set_solver.
          -- destruct Hwr_in' as (sig & v' & Hwr_in').
             exists t', sig, v'.
             split; last done.
             rewrite split_split in Hlookup_i'.
             simpl in Hlookup_i'.
             rewrite lookup_app_Some in Hlookup_i'.
             destruct Hlookup_i' as [Hlookup_i'|Hlookup_i'].
             ++ rewrite Heq_pre in Hlookup_i'.
                rewrite split_split in Hlookup_i'.
                simpl in Hlookup_i'.
                rewrite lookup_app_Some in Hlookup_i'.
                destruct Hlookup_i' as [Hlookup_i'|Hlookup_i'].
                ** apply lookup_lt_Some in Hlookup_i'.
                    rewrite split_length_l in Hlookup_i'.
                    lia.
                ** apply elem_of_list_lookup.
                   set_solver.
             ++ exfalso.
                rewrite split_split in Hlookup_j.
                rewrite lookup_app_Some in Hlookup_j.
                destruct Hlookup_j as [Hlookup_j|Hlookup_j].
                ** apply lookup_lt_Some in Hlookup_j.
                   lia.
                ** rewrite list_lookup_singleton_Some in Hlookup_j.
                   rewrite list_lookup_singleton_Some in Hlookup_i'.
                   lia.
    - intros t1 t2 i j Hlookup_i Hlookup_j Heq.
      rewrite split_split in Hlookup_i; simpl in Hlookup_i.
      rewrite split_split in Hlookup_j; simpl in Hlookup_j.
      rewrite lookup_snoc_Some in Hlookup_i.
      rewrite lookup_snoc_Some in Hlookup_j.
      destruct Hvalid as (_ & _ &  _ & Hvalid).
      destruct Hlookup_i as [Hlookup_i|(Hlength_i & Heq_i)]; 
        destruct Hlookup_j as [Hlookup_j|Hlookup_j].
      1, 4 : set_solver.
      all : subst.
      all : exfalso.
      all : apply Hnin.
      all : apply Hbased.
      all : split; first (apply elem_of_list_lookup; set_solver).
      all : intros Hfalse; destruct trans; set_solver.
  Qed.

  Lemma rel_exec_map_cm_imp (exec : execution) (trans : transaction) (s : signature) (st : state) 
  (m m' : gmap Key (list val)) (mc : gmap Key (option val * bool)) : 
    (∀ k, (∃ v, mc !! k = Some (Some v, true) ∧ latest_write_trans k v trans) ∨ 
      ((¬∃ v, mc !! k = Some (Some v, true)) ∧ (¬∃ sig v, (Wr sig k v ∈ trans)))) →
    (∀ k, k ∈ KVS_keys → is_Some (m !! k)) →
    (∀ k, k ∈ KVS_keys → is_Some (m' !! k)) →
    (dom m = dom m') →
    (∀ k, mc !! k = None → (m' !! k = m !! k)) →
    (∀ k (y1 : aux_defs.Hist) (y2 : option val * bool), 
      m !! k = Some y1 → mc !! k = Some y2 → m' !! k = Some (aux_defs.commit_event y2 y1)) →
    optional_applied_transaction exec st (trans ++ [Cm s true]) →
    valid_execution commit_test_si exec →
    rel_exec_map exec m → 
    rel_exec_map (exec ++ [(trans ++ [Cm s true], st)]) m'.
  Proof.
    intros Hwrites_mc His_some_m His_some_m' Hdom Hnone_mc Hsome_mc Hstate Hvalid_exec Hrel.
    exists st.
    destruct Hstate as [(s' & t' & Hlast & Happlied)|(Hfalse & _)]; last first.
    {
      exfalso.
      destruct Hvalid_exec as (_ & Hvalid_exec & _).
      apply last_None in Hfalse.
      subst.
      set_solver.
    }
    split_and!.
    - rewrite split_split; simpl.
      by rewrite last_snoc.
    - destruct Hrel as (s'' & Hlast' & Hrel & _).
      apply last_Some in Hlast.
      destruct Hlast as (exec' & Heq_exec).
      subst.
      rewrite split_split in Hlast'.
      simpl in Hlast'.
      rewrite last_snoc in Hlast'.
      assert (s' = s'') as ->; first set_solver.
      intros k ov Hk_in.
      destruct (m !! k) as [h|] eqn:Heq; last first.
      {
        specialize (His_some_m k Hk_in).
        rewrite Heq /is_Some in His_some_m.
        set_solver.
      }
      assert (¬ (∃ v, mc !! k = Some (Some v, true)) → m' !! k = m !! k) as Himp.
      {
        intros Hnot.
        destruct (mc !! k) as [(p1, p2)|] eqn:Hlookup; last set_solver.
        destruct (m' !! k) as [h'|] eqn:Heq'; last first.
        {
          specialize (His_some_m' k Hk_in).
          rewrite Heq' /is_Some in His_some_m'.
          set_solver.
        }
        specialize (Hsome_mc k h (p1, p2) Heq Hlookup).
        simpl in Hsome_mc.
        destruct p1 as [v|]; last set_solver.
        destruct p2; set_solver.
      }
      destruct Happlied as (Happlied1 & Happlied2).
      split.
      + intros Hlookup.
        destruct ov as [v|].
        * specialize (Happlied1 k v Hlookup).
          destruct (Hwrites_mc k) as [(v' & Hlookup_mc & Hlatest)|Hwrites_mc'].
          -- destruct Happlied1 as (Happlied1 & Happlied1').
             assert (latest_write_trans k v' (trans ++ [Cm s true])) as Hlatest'; 
              first by apply latest_write_imp_cm.
             specialize (Happlied1 v' Hlatest').
             subst.
             specialize (Hsome_mc k h (Some v', true) Heq Hlookup_mc).
             simpl in Hsome_mc.
             exists (h ++ [v']).
             rewrite last_snoc.
             set_solver.
          -- assert (m' !! k = m !! k) as Heq'; first set_solver.
             exists h.
             rewrite -Heq.
             split; first done.
             assert (s'' !! k = Some v) as Hlookup'; first set_solver.
             specialize (Hrel k (Some v) Hk_in).
             set_solver.
        * destruct (Hwrites_mc k) as [(v' & Hlookup_mc & Hlatest)|Hwrites_mc'].
          -- assert (k ∈ dom st) as Hdom_in.
             {
               apply Happlied2; left.
               rewrite /latest_write_trans in Hlatest.
               set_solver.
             }
             apply not_elem_of_dom_2 in Hlookup.
             set_solver.
          -- assert (m' !! k = m !! k) as Heq'; first set_solver.
             destruct (last h) as [v|] eqn:Hlast; last first.
             {
               exists h; split; last done.
               rewrite -Heq; set_solver.
             }
             assert (s'' !! k = Some v) as Hlookup'; first set_solver.
             assert (k ∈ dom s'') as Hdom_in.
             {
              apply elem_of_dom.
              rewrite /is_Some.
              set_solver.
             }
             assert (k ∈ dom st) as Hdom_in'; first by (apply Happlied2; right).
             apply not_elem_of_dom_2 in Hlookup.
             set_solver.
      + intros (h' & Hlookup & Hlast_h).
        destruct (st !! k) as [v|] eqn:Hlookup_st.
        * destruct (Hwrites_mc k) as [(v' & Hlookup_mc & Hlatest)|Hwrites_mc'].
          -- specialize (Hsome_mc k h (Some v', true) Heq Hlookup_mc).
             simpl in Hsome_mc.
             assert (h' = h ++ [v']) as ->; first set_solver.
             rewrite last_snoc in Hlast_h.
             rewrite -Hlast_h.
             assert (v = v') as ->; last done.
             specialize (Happlied1 k v Hlookup_st).
             destruct Happlied1 as (Happlied1 & Happlied1').
             assert (latest_write_trans k v' (trans ++ [Cm s true])) as Hlatest'; last set_solver.
             by apply latest_write_imp_cm.
          -- assert (m' !! k = m !! k) as Heq'; first set_solver.
             assert (s'' !! k = Some v) as Hlookup'; first set_solver.
             destruct (Hrel k (Some v) Hk_in) as (Hrel' & _).
             apply Hrel' in Hlookup'.
             destruct Hlookup' as (h'' & Hlookup_h'' & Hlast_h'').
             rewrite -Hlast_h'' -Hlast_h. 
             assert (Some h'' = Some h'); last set_solver.
             rewrite -Hlookup_h'' -Hlookup.
             set_solver.
        * destruct ov as [v|]; last done.
          exfalso.
          destruct (Hwrites_mc k) as [(v' & Hlookup_mc & Hlatest)|Hwrites_mc'].
          -- assert (k ∈ dom st) as Hdom_in.
             {
               apply Happlied2; left.
               rewrite /latest_write_trans in Hlatest.
               set_solver.
             }
             apply not_elem_of_dom_2 in Hlookup_st.
             set_solver.
          -- assert (m' !! k = m !! k) as Heq'; first set_solver.
             assert (s'' !! k = Some v) as Hlookup'.
             {
               apply (Hrel k (Some v) Hk_in).
               exists h'.
               split; last done.
               rewrite -Hlookup.
               set_solver.
             }
             assert (k ∈ dom s'') as Hdom_in.
             {
              apply elem_of_dom.
              rewrite /is_Some.
              set_solver.
             }
             assert (k ∈ dom st) as Hdom_in'; first by (apply Happlied2; right).
             apply not_elem_of_dom_2 in Hlookup_st.
             set_solver.
    - intros k h Hlookup.
      assert (exec ≠ []) as Hneq.
      {
        apply last_Some_elem_of in Hlast.
        intros ->.
        set_solver.
      }
      destruct (m !! k) as [h'|] eqn:Heq'; last first.
      {
        apply not_elem_of_dom_2 in Heq'.
        assert (k ∉ dom m') as Hdom2; first set_solver.
        apply not_elem_of_dom_1 in Hdom2.
        set_solver.
      }
      destruct (Hwrites_mc k) as [(v & Hlookup_mc & Hlatest)|Hwrites_mc'].
      + specialize (Hsome_mc k h' (Some v, true) Heq' Hlookup_mc).
        simpl in Hsome_mc.
        assert (h = h' ++ [v]) as ->; first set_solver.
        apply Rel_exec_map_app1; try done.
        * rewrite /latest_write_trans in Hlatest.
          set_solver.
        * destruct Hrel as (st' & _ & _ & Hrel).
          set_solver.
      + apply Rel_exec_map_app2; try done; first set_solver.
        destruct Hrel as (st' & Hlast_st' & Hst_reads & Hrel).
        apply Hrel.
        destruct (mc !! k) as [(p1, p2)|] eqn:Heq; last by rewrite -(Hnone_mc k Heq).
        rewrite -Hlookup.
        rewrite (Hsome_mc k h' (p1, p2) Heq' Heq).
        destruct p2; simpl; destruct p1 as [v|]; set_solver.
  Qed.

  Lemma inv_ext_si_wr_imp1 (γm_gl γexec γsi_name γm_conn γsnap : gname) (T1 T2 : list transaction) 
  (exec : execution) (extract : val → option val) (clients : gset socket_address) (sa : socket_address) trans tag c k v :
    k ∈ KVS_keys →
    extract c = Some #sa →
    clients = {[sa]} ∪ clients ∖ {[sa]} →
    valid_transactions (T1 ++ (trans ++ [Wr (tag, c) k v]) :: T2) →
    ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)) -∗
    ⌜∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false ⌝ -∗
    GlobalInvExtSI γm_gl γexec γsi_name (T1 ++ trans :: T2) exec extract clients -∗
    GlobalInvExtSI γm_gl γexec γsi_name (T1 ++ (trans ++ [Wr (tag, c) k v]) :: T2) exec extract clients.
  Proof.
    iIntros (Hk_in Hextract Heq_sa_clients Hvalid) "#Hsa_pointer %Hop
      (%mnames & Hghost_map_mnames & %m_gl & Hghost_map_mgl & #Hkeys_some & Hexec & #Hrel_exec & Hopen_state)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mnames][$Hsa_pointer]") as "%Hlookup_mnames".
    iExists mnames; iFrame.
    iExists m_gl; iFrame.
    iFrame "#".
    rewrite /open_transactions_state.
    rewrite Heq_sa_clients.
    do 2 (rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver).
    iDestruct "Hopen_state" as "(Hopen_state_sa & Hopen_state)".
    iSplitL "Hopen_state_sa".
    - do 2 rewrite big_sepS_singleton.
      iDestruct "Hopen_state_sa" as "[Hopen_state_sa|(%c' & %m_conn' & %γm_conn' & %γsnap' & 
        (%Hextract' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
      iRight.
      iExists c', m_conn', γm_conn', γsnap'.
      iSplit; first done.
      iFrame.
      iPureIntro.
      intros trans' Hopen.
      assert (c = c') as <-; first set_solver.
      assert (trans ++ [Wr (tag, c) k v] = trans') as <-.
      {
        eapply trans_eq; try done.
        rewrite last_snoc.
        exists (Wr (tag, c) k v).
        split_and!; try set_solver.
      }
      assert (open_trans trans c (T1 ++ trans :: T2)) as Hopen'.
      {
        destruct Hop as (op & Hop).
        exists op.
        split_and!; rewrite /is_cm_op; try set_solver.
      }
      specialize (Hopen_state trans Hopen'). 
      destruct Hopen_state as (Hopen_state_1 & Hopen_state_2).
      split.
      {
        intros sig k' ov v' [Hop_in|Hop_in]; rewrite elem_of_app in Hop_in.
        - destruct Hop_in as [Hop_in|Hfalse]; last set_solver.
          eapply Hopen_state_1; left; set_solver.
        - destruct Hop_in as [Hop_in|Hop_in].
          + eapply Hopen_state_1; right; set_solver.
          + assert (k' = k) as ->; set_solver.
      }
      intros s k' v' Hin.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hfalse]; last set_solver.
      specialize (Hopen_state_2 s k' v' Hin).
      intros Hnot_exists.
      apply Hopen_state_2.
      intros (sig' & v'' & Hrel).
      apply Hnot_exists.
      exists sig', v''.
      by apply rel_list_imp.
    - iApply (big_sepS_wand with "[$Hopen_state]").
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa' Hsa'_in).
      iIntros "[Hopen_state_sa|(%c' & %m_conn' & %γm_conn' & %γsnap' & 
        (%Hextract' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
      iRight.
      iExists c', m_conn', γm_conn', γsnap'.
      iSplit; first done.
      iFrame.
      iPureIntro.
      intros trans' Hopen.
      assert (open_trans trans' c' (T1 ++ trans :: T2)) as Hopen'. 
      {
        eapply (open_trans_neq3 _ sa sa' c c' _ _ _ _ (Wr (tag, c) k v)); rewrite /connOfOp; set_solver.
      }
      specialize (Hopen_state trans' Hopen').
      set_solver.
      Unshelve.
      all : done.
  Qed.

  Lemma inv_ext_si_wr_imp2 (γm_gl γexec γsi_name γm_conn γsnap : gname) (T : list transaction) 
  (exec : execution) (extract : val → option val) (clients : gset socket_address) (sa : socket_address) tag c k v :
    k ∈ KVS_keys →
    extract c = Some #sa →
    clients = {[sa]} ∪ clients ∖ {[sa]} →
    valid_transactions (T ++ [[Wr (tag, c) k v]]) →
    ghost_map_elem γsi_name sa DfracDiscarded (Some (γm_conn, γsnap, c)) -∗
    GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients -∗
    GlobalInvExtSI γm_gl γexec γsi_name (T ++ [[Wr (tag, c) k v]]) exec extract clients.
  Proof.
    iIntros (Hk_in Hextract Heq_sa_clients Hvalid) "#Hsa_pointer 
      (%mnames & Hghost_map_mnames & %m_gl & Hghost_map_mgl & #Hkeys_some & Hexec & #Hrel_exec & Hopen_state)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mnames][$Hsa_pointer]") as "%Hlookup_mnames".
    iExists mnames; iFrame.
    iExists m_gl; iFrame.
    iFrame "#".
    rewrite /open_transactions_state.
    rewrite Heq_sa_clients.
    do 2 (rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver).
    iDestruct "Hopen_state" as "(Hopen_state_sa & Hopen_state)".
    iSplitL "Hopen_state_sa".
    - do 2 rewrite big_sepS_singleton.
      iDestruct "Hopen_state_sa" as "[Hopen_state_sa|(%c' & %m_conn' & %γm_conn' & %γsnap' & 
        (%Hextract' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
      iRight.
      iExists c', m_conn', γm_conn', γsnap'.
      iSplit; first done.
      iFrame.
      iPureIntro.
      intros trans Hopen.
      assert ([Wr (tag, c) k v] = trans) as <-.
      {
        eapply (trans_eq); try done.
        exists (Wr (tag, c) k v).
        split_and!; set_solver.
      }
      split; last set_solver.
      intros s k' ov' v' [Hin|Hin]; first set_solver.
      assert (k = k') as ->; set_solver.
    - iApply (big_sepS_wand with "[$Hopen_state]").
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa' Hsa'_in).
      iIntros "[Hopen_state_sa|(%c' & %m_conn' & %γm_conn' & %γsnap' & 
        (%Hextract' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
      iRight.
      iExists c', m_conn', γm_conn', γsnap'.
      iSplit; first done.
      iFrame.
      iPureIntro.
      intros trans Hopen.
      assert (open_trans trans c' T) as Hopen'.
      {
        eapply (open_trans_neq1 _ sa sa' c c'); rewrite /connOfOp; set_solver.
      }
      specialize (Hopen_state trans Hopen').
      set_solver.
  Qed.

  Lemma open_transactions_state_cm_imp T1 T2 trans mnames_si s b extract clients: 
    open_transactions_state (T1 ++ trans :: T2) mnames_si extract clients -∗
    open_transactions_state (T1 ++ (trans ++ [Cm s b]) :: T2) mnames_si extract clients.
  Proof.
    iIntros "Hopen".
    rewrite /open_transactions_state.
    iApply (big_sepS_wand with "Hopen").
    iApply big_sepS_intro.
    iModIntro.
    iIntros (sa Hsa_in) "Hopen".
    destruct (mnames_si !! sa) as [opt|]; 
      last (iDestruct "Hopen" as "[%Hopen|(%c & %m_conn & %γ_conn & %γsnap & %Hfalse & _)]"; set_solver).
    destruct opt as [opt|]; last set_solver.
    iRight.
    iDestruct "Hopen" as "[%Hfalse|(%c & %m_conn & %γ_conn & %γsnap & %Hextract & Hghost_map & %Hreads)]"; 
      first set_solver.
    iExists c, m_conn, γ_conn, γsnap.
    iFrame "%∗".
    iPureIntro.
    intros trans' (op & Htrans'_in & Hopen).
    specialize (Hreads trans').
    rewrite elem_of_app in Htrans'_in.
    destruct Htrans'_in as [Htrans'_in|Htrans'_in].
    - apply Hreads.
      rewrite /open_trans.
      exists op; set_solver. 
    - rewrite elem_of_cons in Htrans'_in.
      destruct Htrans'_in as [Htrans'_in|Htrans'_in].
      + exfalso. 
        subst.
        rewrite last_snoc /is_cm_op in Hopen.
        set_solver.
      + apply Hreads.
        rewrite /open_trans.
        exists op; set_solver. 
  Qed.
  
  (** Per operation implications *)

  Lemma commit_implication γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hcommit".
    rewrite /commit_spec.
    iModIntro.
    iIntros (c sa E) "%Hsub (#Hconn & %Hsa_in_clients & %Hsa_extract & (%γ & #Hsa_pointer & #Hsa_pointer_si)) !# %Φ Hshift".
    rewrite /TC_commit /KVS_wrapped_api /wrap_commit.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /commit_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%exec (Hinv_si_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_cm_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"CmPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"CmPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Hinv_si_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"CmPre"))%V]), lt.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_cm_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hcommit"; try done.
    iClear "Hcommit".
    iMod "Hshift" as "(%m & %ms & %mc & ((Hconn_state & %γm_conn & %γsnap & %m_conn & #Hsa_pointer_si' & Hghost_map_m_conn &
      Hconn_exec_state) & %Hdom1 & %Hdom2 & Hkeys & Hkeys_conn) & Hshift)".
    iModIntro.
    iExists m, ms, mc.
    rewrite big_sepM_sep.
    iDestruct "Hkeys_conn" as "(Hkeys_conn1 & Hkeys_conn2)".
    simpl.
    do 4 rewrite big_sepM_sep.
    iDestruct "Hkeys" as "(Hkeys_orig & Hkeys & #Hkeys_hist)".
    iDestruct "Hkeys_conn1" as "(Hkeys_conn1_orig & Hkeys_conn1)".
    iDestruct "Hkeys_conn2" as "(Hkeys_conn2_orig & Hkeys_conn2)".
    iSplitL "Hconn_state Hkeys_orig Hkeys_conn1_orig Hkeys_conn2_orig".
    {
      rewrite big_sepM_sep.
      iFrame.
      iSplit; by iPureIntro.
    }
    iModIntro.
    iIntros (b) "(Hconn_state & Hkeys_disj)".
    iInv "HinvExt" as ">[%T' [%exec' (Hinv_si_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"CmLin", #b)))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"CmPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"CmPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"CmLin", #b)))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hstate_res'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {5} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iDestruct "Htrace_res" as "(%loc_st & %c' & %γ' & %m' & %Hlookup_mstate & %Hextract & #Hsa_pointer'
      & Hmap_m & Htrace_res)".
    iDestruct "Hconn_exec_state" as "[(%Hfalse & _)|(%ms_conn & %ms_conn_sub & %Hdom3 & %Hdom4 & %exec_pre & 
      #Hexec_hist & %Hrel_exec_pre & Hstate_pr & Hkeys_conn_unused)]"; first (exfalso; set_solver).
    iAssert (⌜loc_st = Active (dom ms)⌝)%I as "->".
    {
      iDestruct (@ghost_map_lookup with "[$Hmap_mstate][$Hstate_pr]") as "%Hlookup_mstate'".
      iPureIntro.
      set_solver.
    }
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa_pointer][$Hsa_pointer']").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(%Hfalse & _ & _)|Htrace_res])"; first done.
    iMod (ghost_map_update (CanStart, Some c) with "[$Hmap_mstate] [$Hstate_pr]") 
      as "(Hmap_mstate & Hstate_pr)".
    iAssert ([∗ map] k↦p ∈ mc, (∀ v, ⌜p.1 = Some v⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
      ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I 
      as "#Hkeys_conn_lin_hist".
    {
      iApply (big_sepM_wand with "[$Hkeys_conn1]").
      iApply big_sepM_intro.
      iModIntro.
      iIntros (k p Hlookup) "(%sa' & %γ' & %ov & _ & _ & _ & _ & Hlin_hist & _)".
      iFrame.
    }
    assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
      op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
      as Hdecision.
    {
      do 2 (apply list_exist_dec; intros).
      apply _.
    }
    assert (∀ k : Key, is_Some (m !! k) ↔ is_Some (mc !! k)) as His_some.
    {
      intros k; split; intros His_some.
      all : rewrite -elem_of_dom.
      all : rewrite -elem_of_dom in His_some.
      all : set_solver.
    }
    assert (lin_trace_of (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]) t') as Hlin_of_add.
    {
      apply (lin_trace_lin lt' (#tag1, (c, #"CmPre"))%V 
        (#tag1, (c, (#"CmLin", #b)))%V tag1 c t'); try done;
        rewrite /is_lin_event /is_cm_lin_event /is_pre_event /is_cm_pre_event;
        set_solver.
    }
    iAssert (⌜valid_sequence (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V])⌝)%I as "%Hvalid_seq_add".
    {
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & Hact_eq & -> & 
        %Hopen_start & Hrest)".
      iPureIntro.
      apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done; last by exists t'.
      rewrite /is_cm_lin_event; set_solver.
    }
    destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
      op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as [(trans & Htrans_in & Hop)|Hdec].
    - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
      iDestruct "Hinv_si_res'" as "(%mnames_si & Hghost_map_mnames_si & %m_gl & Hghost_map_m_gl & %His_some_keys &
        Hown_exec & %Hrel_exec_m_gl & Hopen_trans)".
      rewrite /OwnExec /OwnExecHist.
      iDestruct (own_obs_prefix γexec 1 exec' exec_pre with "[$Hown_exec][$Hexec_hist]") as "%Hpre_exec".
      iAssert (⌜∀ s k ov, (Rd s k ov) ∈ trans → 
        ¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k ov)) →
        reads_from_last_state exec_pre k ov⌝)%I as "%Htrans_reads".
      {
        rewrite /open_transactions_state.
        rewrite {4} Heq_sa_clients.
        rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
        iDestruct "Hopen_trans" as "(Hopen_trans & _)".
        rewrite big_sepS_singleton.
        iDestruct (@ghost_map_lookup with "[$Hghost_map_mnames_si][$Hsa_pointer_si']") as "%Hlookup_mnames_si".
        iDestruct "Hopen_trans" as "[%Hfalse|(%c_sa & %m_conn_sa & %γm_conn_sa & %γsnap_sa & %Hextract_c_sa 
          & Hghost_map_m_conn_sa & %Hopen_state)]"; first set_solver.
        iIntros (s k ov Hread_in Hnot).
        assert (c = c_sa) as <-; first set_solver.
        assert (open_trans trans c (T1 ++ trans :: T2)) as Hopen.
        {
          destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
          exists op.
          split_and!; try done.
          rewrite /is_cm_op.
          destruct op; set_solver.
        }
        rewrite /reads_from_last_state.
        assert (m_conn_sa !! k = (Some ov)) as Hlookup_mc_conn_sa; first by eapply Hopen_state.
        destruct Hrel_exec_pre as ((st' & Hlast_st' & Hreads_st' & _) & Hsub').
        iExists st'.
        iSplit; first done.
        assert (γm_conn = γm_conn_sa) as <-; first set_solver.
        iDestruct (@ghost_map.ghost_map_auth_agree _ Key (option val) 
          with "[$Hghost_map_m_conn][$Hghost_map_m_conn_sa]") as "<-".
        assert (k ∈ KVS_keys) as Hk_in.
        {
          destruct (Hopen_state trans Hopen) as (Hopen_state' & _).
          by eapply Hopen_state'; left.
        }
        destruct (decide (k ∈ dom ms_conn_sub)) as [Hk_in_dom|Hk_in_dom]; last first.
        {
          assert (k ∈ (KVS_keys ∖ (dom ms_conn_sub ∩ KVS_keys))) as Hdom5; first set_solver.
          rewrite (big_sepS_delete _ _ k); last done.
          iDestruct "Hkeys_conn_unused" as "((%Hkey_conn & _) & _)".
          set_solver.
        }
        destruct (Hdom4 k ov Hk_in Hk_in_dom Hlookup_mc_conn_sa) as (h & Hlookup_ms_conn_sub & Hlast_h).
        iPureIntro.
        assert (ms_conn !! k = Some h) as Hlookup_mc_conn; first by eapply lookup_weaken.
        destruct (Hreads_st' k ov Hk_in) as (_ & Hreads_st'').
        apply Hreads_st''.
        eauto.
      }
      iAssert (⌜∀ s k v, Wr s k v ∈ trans → ∃ h, ms_conn !! k = Some h ∧ m_gl !! k = Some h⌝)%I as "%Htrans_writes".
      {
        admit.
      }
      iAssert (⌜∀ k, (∃ v, mc !! k = Some (Some v, true) ∧ latest_write_trans k v trans) ∨ 
        ((¬∃ v, mc !! k = Some (Some v, true)) ∧ (¬∃ sig v, (Wr sig k v ∈ trans)))⌝)%I as "%Hcm_writes".
      {
        admit.
      }
      destruct (optional_applied_transaction_exists exec' (trans ++ [Cm (tag1, c) b])) as (st & Happl).
      iAssert ([∗ map] k↦x ∈ mc, 
        (∃ (sa : socket_address) (γ : gname) (ov_last_wr : option val), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
          ⌜extract c = Some #sa⌝ ∗ ⌜sa ∈ clients⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov_last_wr)) ∗
        (∃ (sa : socket_address) (γ : gname) (ov_last_wr : option val), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
          ⌜extract c = Some #sa⌝ ∗ ⌜sa ∈ clients⌝ ∗ (⌜k ∈ KVS_keys⌝ → local_key_state γsi_name γl sa c k x.1 ov_last_wr))
        )%I with "[Hkeys_conn1]" as "Hkeys_conn1".
      {
        iApply (big_sepM_wand with "[$Hkeys_conn1]").
        iApply big_sepM_intro.
        iModIntro.
        iIntros (k p Hlookup) "(%sa' & %γ' & %ov_last_wr & #Hsa'_pointer & %Hsa'_extract & Hkey & %Hsa'_in & 
          _ & Hkey_state)".
        iSplitL "Hkey"; iExists sa', γ', ov_last_wr; iFrame "#%∗".
      }
      rewrite (big_sepM_sep _ _ mc).
      iDestruct "Hkeys_conn1" as "(Hkeys_conn1 & Hkeys_conn1')".
      iAssert (|==>(((⌜b = false⌝ ∗ ghost_map_auth γm_gl 1 m_gl) ∨ 
        (⌜b = true⌝ ∗ (∃ m_gl', ghost_map_auth γm_gl 1 m_gl' ∗ ⌜dom m_gl = dom m_gl'⌝ ∗
          ⌜∀ k, mc !! k = None → m_gl' !! k = m_gl !! k⌝ ∗
          ⌜∀ k y1 y2, m_gl !! k = Some y1 → mc !! k = Some y2 → m_gl' !! k = Some (aux_defs.commit_event y2 y1)⌝))) ∗ 
        ((⌜b = false⌝  ∗ ([∗ map] k↦x ∈ m, ghost_map_elem γm_gl k (DfracOwn 1%Qp) x)) ∨ 
        (⌜b = true⌝ ∗ ([∗ map] k↦y1;y2 ∈ m;mc, ghost_map_elem γm_gl k (DfracOwn 1%Qp) (aux_defs.commit_event y2 y1))))))%I 
        with "[Hkeys Hghost_map_m_gl]" as ">(Hghost_map_m_gl & Hkeys)".
      {
        destruct b; last (iModIntro; iSplitL "Hghost_map_m_gl"; iLeft;  by iFrame).
        iAssert (⌜dom m = dom mc⌝)%I as "#Hdom_mc"; first (iPureIntro; set_solver).
        iClear "Hkeys_hist Hkeys_conn_lin_hist".
        clear Hdom1 Hdom2 His_some Hcm_writes Htrans_writes Htrans_reads.
        iRevert "Hdom_mc".
        iInduction m as [|k x m Hlookup_k_m] "IH" using map_ind forall (mc).
        - iIntros (Hdom_mc).
          iModIntro.
          rewrite dom_empty_L in Hdom_mc.
          assert (mc = ∅) as ->; first by apply dom_empty_inv_L. 
          iSplitL "Hghost_map_m_gl". 
          + iRight.
            iSplit; first done.
            iExists m_gl; iFrame.
            iSplit; first done.
            iSplit; first (iPureIntro; set_solver).
            iPureIntro; set_solver.
          + iRight; iSplit; first done.
            set_solver.
        - iIntros (Hdom_mc).
          rewrite {1} big_sepM_insert; last done.
          iDestruct "Hkeys" as "(Hkey & Hkeys)".
          destruct (mc !! k) as [(p1, p2)|] eqn:Hlookup_k_mc; last first.
          {
            apply not_elem_of_dom_2 in Hlookup_k_mc.
            rewrite dom_insert_L in Hdom_mc.
            set_solver.
          }
          assert (mc = <[k:=(p1, p2)]> (delete k mc)) as Hdel_mc_eq.
          {
            apply eq_sym.
            by apply (insert_delete mc k (p1, p2)).
          }
          rewrite Hdel_mc_eq in Hdom_mc.
          do 2 rewrite dom_insert_L in Hdom_mc.
          iDestruct (@ghost_map_lookup with "[$Hghost_map_m_gl][$Hkey]") as "%Hlookup_m_gl".
          iDestruct ("IH" $! (delete k mc) with "[$Hkeys][$Hghost_map_m_gl][]") as 
            ">([(%Hfalse & _)|(_ & (%m_gl' & Hghost_map_m_gl' & %Hdom' & %Himp1 & %Himp2))] & Hkeys)".
          {
            iModIntro; iPureIntro.
            apply not_elem_of_dom_2 in Hlookup_k_m.
            destruct ((delete k mc) !! k) as [v|] eqn:Hlookup_del; 
              first (rewrite lookup_delete in Hlookup_del; set_solver).
            apply not_elem_of_dom_2 in Hlookup_del.
            apply (union_cancel_l_L _ _ {[k]}); set_solver.
          }
          set_solver.
          iDestruct "Hkeys" as "[(%Hfalse & _) | (_ & Hkeys)]"; first set_solver.
          iMod (@ghost_map_update _ Key (list val) _ _ _ _ _ k x (aux_defs.commit_event (p1, p2) x) 
            with "[$Hghost_map_m_gl'] [$Hkey]") as "(Hghost_map_m_gl' & Hkey)".
          iModIntro.
          iSplitR "Hkey Hkeys"; iRight; (iSplit; first done).
          + iExists (<[k:=aux_defs.commit_event (p1, p2) x]> m_gl').
            iFrame.
            iPureIntro; split_and!.
            * rewrite -(insert_id _ _ _ Hlookup_m_gl).
              do 2 rewrite dom_insert_L.
              set_solver.
            * intros k' Hnone.
              destruct (decide (k = k')) as [<-|Hneq]; first set_solver.
              rewrite lookup_insert_ne; last done.
              apply Himp1.
              by rewrite lookup_delete_ne.
            * intros k' x' (p1', p2') Hlookup_k'_m_gl Hlookup_k'_mc.
              destruct (decide (k = k')) as [<-|Hneq].
              -- rewrite lookup_insert.
                 rewrite Hlookup_m_gl in Hlookup_k'_m_gl.
                 rewrite Hlookup_k_mc in Hlookup_k'_mc.
                 set_solver.
              -- rewrite lookup_insert_ne; last done. 
                 apply Himp2; try done.
                 by rewrite lookup_delete_ne.
          + rewrite {2} Hdel_mc_eq.
            rewrite big_sepM2_insert; try done; last apply lookup_delete.
            iFrame.
      }
      iAssert (|==> ((⌜b = false⌝ ∗ own_log_auth γexec 1 exec') ∨ 
        (⌜b = true⌝ ∗ own_log_auth γexec 1 (exec' ++ [(trans ++ [Cm (tag1, c) true], st)]))))%I 
        with "[Hown_exec]" as ">Hown_exec".
      {
        destruct b.
        - iMod (own_log_auth_update _ _ (exec' ++ [(trans ++ [Cm (tag1, c) true], st)]) with "[$Hown_exec]") 
            as "Hown_exec"; first by apply prefix_app_r.
          iModIntro; iRight.
          by iFrame.
        - iModIntro; iLeft.
          by iFrame.
      }
      iMod ("Hclose'" with "[Hghost_map_m_gl Htr_is' HOwnLin' Hpost_res' Hlin_res' Htrace_res Hmap_mname
        Hmap_m Hdisj_trace_res Hmap_mstate Hkeys_conn1 Hghost_map_mnames_si Hown_exec Hopen_trans]").
      {
        iModIntro.
        iExists (T1 ++ (trans ++ [Cm (tag1, c) b]) :: T2), (optionalExtendExecution exec' (trans ++ [Cm (tag1, c) b]) st); iFrame.
        iSplitL "Hghost_map_m_gl Hghost_map_mnames_si Hown_exec Hopen_trans".
        {
          iExists mnames_si; iFrame.
          iDestruct (open_transactions_state_cm_imp with "[$Hopen_trans]") as "Hopen_trans".
          iDestruct "Hghost_map_m_gl" as "[(-> & Hghost_map_m_gl) | (-> & (%m_gl' & Hghost_map_m_gl & %Hdom5 &
            (%Hm_gl'_reads_none & %Hm_gl'reads_some)))]".
          - iExists m_gl; iFrame "%∗".
            rewrite /optionalExtendExecution last_snoc /OwnExec.
            iDestruct "Hown_exec" as "[(_ & Hown_exec)|(%Hfalse & _)]"; last set_solver.
            iFrame "∗%".
          - iExists m_gl'; iFrame "%∗".
            assert (∀ k, k ∈ KVS_keys → is_Some (m_gl' !! k)) as His_some_keys'.
            {
              intros k Hk_in.
              specialize (His_some_keys k Hk_in).
              rewrite -elem_of_dom.
              rewrite -elem_of_dom in His_some_keys.
              set_solver.
            }
            iFrame "%".
            rewrite /optionalExtendExecution last_snoc /OwnExec.
            iDestruct "Hown_exec" as "[(%Hfalse & _)|(_ & Hown_exec)]"; first set_solver.
            iFrame.
            iPureIntro.
            apply (rel_exec_map_cm_imp exec' trans (tag1, c) st m_gl m_gl' mc); try done.
        }
        iExists t', (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]).
        iFrame.
        iSplit; first done.
        iSplit; first (iPureIntro; by apply trans_add_non_empty).
        iSplit; first (iPureIntro; by apply extraction_of_add2).
        iSplit.
        - iPureIntro.
          apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
          + by eapply extraction_of_not_in.
          + by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
          + destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
            exists op.
            split_and!; try done.
            intros (s' & b' & ->).
            set_solver.
        - iSplit; first done.
          iSplit; first (iPureIntro; apply based_on_add4; set_solver).
          iSplit.
          + iPureIntro.
            rewrite /optionalExtendExecution last_snoc.
            destruct b; last done.
            eapply (valid_execution_si_imp exec_pre ms_conn exec'); try done.
            * set_solver.
            * intros Hfalse.
              apply Hnot_lin_in.
              exists (toLinEvent (Cm (tag1, c) true)).
              simpl.
              destruct Hex' as (_ & Hex' & _).
              split; last done.
              apply (Hex' (trans ++ [Cm (tag1, c) true]) (Cm (tag1, c) true)); last set_solver.
              by apply com_trans_imp2.
          + iAssert (∃ (mc' : gmap Key (option val)), ⌜dom mc' = dom mc⌝ ∗ 
              ([∗ map] k↦x ∈ mc', ∃ (sa : socket_address) γ, ghost_map_elem γmname sa DfracDiscarded (γ,c) ∗ 
                ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) x) ∗ ⌜sa ∈ clients⌝))%I 
              with "[Hkeys_conn1]" as "(%mc' & %Hdom5 & Hkeys_conn1)".
            {
              iClear "Hkeys_conn_lin_hist".
              clear His_some Hdom2 Hcm_writes.
              iInduction mc as [|k x mc Hlookup_k_mc] "IH" using map_ind. 
              - iExists ∅.
                iSplit; last set_solver.
                iPureIntro; set_solver.
              - rewrite big_sepM_insert_delete.
                iDestruct "Hkeys_conn1" as "((%sa' & %γ' & %ov_last & #Hsa'_pointer & %Hextract' & 
                  %Hsa'_in & Hkey) & Hkeys_conn1)".
                rewrite (delete_notin mc); last done.
                iDestruct ("IH" with "[$Hkeys_conn1]") as "(%mc' & %Hdom_mc' & Hkeys_conn1)".
                iExists (<[k:=ov_last]> mc').
                iSplit; first (iPureIntro; set_solver).
                rewrite big_sepM_insert.
                + iFrame.
                  iExists sa', γ'.
                  iFrame "#%∗".
                + apply not_elem_of_dom_1. 
                  apply not_elem_of_dom_2 in Hlookup_k_mc.
                  set_solver.
            }
            iApply (trace_state_resources_commit_lin2 clients c tag1 lt' T1 T2 trans sa 
              (dom ms) γ γmstate γmname extract b mc' mstate mname m' with 
              "[//][][//][//][//][//][//][//][][$Hkeys_conn1][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
              [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
            * iPureIntro; set_solver.
            * iPureIntro.
              destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
              exists e.
              split_and!; try done.
              apply elem_of_app; eauto.
      }
      iMod ("Hshift" with "[Hghost_map_m_conn Hkeys_conn1' Hkeys_conn_unused Hkeys Hkeys_conn2 Hconn_state 
        Hstate_pr Hkeys_disj]").
      {
        iFrame.
        iSplitR "Hkeys_disj Hkeys".
        - iExists γm_conn, γsnap, m_conn.
          iFrame "∗#".
          iLeft.
          iSplit; first done.
          iFrame.
          iClear "Hkeys_conn_lin_hist".
          assert (ms = ms_conn_sub) as <-; first set_solver.
          rewrite Hdom2.
          clear Hdom1 Hdom2 Hdom3 Hdom4 Hrel_exec_pre His_some_keys His_some Hcm_writes.
          iInduction (KVS_keys) as [|k dom_rest Hnin] "IH" using set_ind_L forall (mc); first set_solver.
          rewrite big_sepS_union; last set_solver.
          destruct (decide (k ∈ dom mc)) as [Hk_in | Hk_nin].
          + apply lookup_lookup_total_dom in Hk_in.
            do 2 (rewrite (big_sepM_delete _ mc k (mc !!! k)); last done).
            iDestruct "Hkeys_conn1'" as "(Hkey_conn1 & Hkeys_conn1)".
            iDestruct "Hkeys_conn2" as "(Hkey_conn2 & Hkeys_conn2)".
            iSplitL "Hkey_conn1 Hkey_conn2".
            * rewrite big_sepS_singleton.
              iDestruct "Hkey_conn1" as "(%sa' & %γ' & %ov_last & #Hsa'_pointer & %Hextract' & %Hsa'_in & Hkey1)".
              iDestruct "Hkey_conn2" as "(%sa'' & %γm_conn' & %γsnap' & %Hextract'' & #Hsa''_pointer & Hkey2)".
              assert (sa = sa'') as <-; first set_solver.
              iDestruct (ghost_map_elem_agree sa γsi_name _ _ (Some (γm_conn, γsnap, c)) (Some (γm_conn', γsnap', c)) 
                with "[$Hsa_pointer_si'][$Hsa''_pointer]") as "%Heq_names".
              assert (γm_conn' = γm_conn) as ->; first set_solver.
              assert (γsnap' = γsnap) as ->; first set_solver.
              iDestruct ("Hkey1" with "[]") as "(%γm_conn'' & %γsnap'' & #Hsa'_pointer' & Hkey1)"; first (iPureIntro; set_solver).
              assert (sa = sa') as <-; first set_solver.
              iDestruct (ghost_map_elem_agree sa γsi_name _ _ (Some (γm_conn, γsnap, c)) (Some (γm_conn'', γsnap'', c)) 
                with "[$Hsa_pointer_si'][$Hsa'_pointer']") as "%Heq_names'".
              assert (γm_conn'' = γm_conn) as ->; first set_solver.
              assert (γsnap'' = γsnap) as ->; first set_solver.
              iDestruct ("Hkey2" with "[]") as "[(_ & (%ov' & Hkey2))|(_ & Hkey2)]"; first (iPureIntro; set_solver).
              -- iExists ov'.
                 iDestruct "Hkey1" as "[(_ & Hkey1)|(%v' & _ & Hkey1)]"; last iFrame.
                 iCombine "Hkey1" "Hkey2" as "Hfalse".
                 iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
                 by rewrite dfrac_valid_own in Hfalse.
              -- iDestruct "Hkey1" as "[(_ & Hkey1)|(%v' & _ & Hkey1)]"; first (iExists ((mc !!! k).1); iFrame).
                 iCombine "Hkey1" "Hkey2" as "Hfalse".
                 iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
                 by rewrite dfrac_valid_own in Hfalse.
            * iApply ("IH" $! (delete k mc) with "[Hkeys_conn1][Hkeys_conn_unused][Hkeys_conn2]").
              -- iApply (big_sepM_wand with "[$Hkeys_conn1]").
                 iApply big_sepM_intro.
                 iModIntro.
                 iIntros (k' p Hlookup') "(%sa' & %γ' & %ov_last & #Hsa'_pointer & %Hextract' & %Hsa'_in & Hkey1)".
                 iExists sa', γ', ov_last.
                 iFrame "%#".
                 iIntros (Hk'_in).
                 iApply "Hkey1"; iPureIntro; set_solver.
              -- assert (({[k]} ∪ dom_rest) ∖ (dom mc ∩ ({[k]} ∪ dom_rest)) = dom_rest ∖ (dom (delete k mc) ∩ dom_rest)) 
                  as <-; last iFrame.
                  apply insert_delete in Hk_in.
                  apply eq_sym in Hk_in.
                  rewrite {1} Hk_in.
                  rewrite {1} dom_insert_L.
                  set_solver.
              -- iApply (big_sepM_wand with "[$Hkeys_conn2]").
                 iApply big_sepM_intro.
                 iModIntro.
                 iIntros (k' p Hlookup') "(%sa' & %γm_conn' & %γsnap' & %Hextract'' & #Hsa''_pointer & Hkey2)".
                 iExists sa', γm_conn', γsnap'.
                 iFrame "%#".
                 iIntros (Hk'_in).
                 iApply "Hkey2"; iPureIntro; set_solver.
          + assert ((dom_rest ∖ (dom mc ∩ dom_rest)) ∪ {[k]} = ({[k]} ∪ dom_rest) ∖ (dom mc ∩ ({[k]} ∪ dom_rest))) as <-; 
              first set_solver.
            rewrite big_sepS_union; last set_solver.
            iDestruct "Hkeys_conn_unused" as "(Hkeys_conn_unused & Hkey_conn_unused)".
            iSplitL "Hkey_conn_unused".
            {
              do 2 rewrite big_sepS_singleton.
              iExists None.
              iDestruct "Hkey_conn_unused" as "(%Hlookup & Hkey)".
              iFrame.
              iRight; done.
            }
            iApply ("IH" $! mc with "[Hkeys_conn1'][$Hkeys_conn_unused][Hkeys_conn2]").
            -- iApply (big_sepM_wand with "[$Hkeys_conn1']").
               iApply big_sepM_intro.
               iModIntro.
               iIntros (k' p Hlookup') "(%sa' & %γ' & %ov_last & #Hsa'_pointer & %Hextract' & %Hsa'_in & Hkey1)".
               iExists sa', γ', ov_last.
               iFrame "%#".
               iIntros (Hk'_in).
               iApply "Hkey1"; iPureIntro; set_solver.
            -- iApply (big_sepM_wand with "[$Hkeys_conn2]").
               iApply big_sepM_intro.
               iModIntro.
               iIntros (k' p Hlookup') "(%sa' & %γm_conn' & %γsnap' & %Hextract'' & #Hsa''_pointer & Hkey2)".
               iExists sa', γm_conn', γsnap'.
               iFrame "%#".
               iIntros (Hk'_in).
               iApply "Hkey2"; iPureIntro; set_solver.
        - iDestruct "Hkeys_disj" as "[(-> & %Hcan_com & Hkeys_disj)| (-> & %Hcan_com & Hkeys_disj)]".
          + iLeft.
            do 2 (iSplit; first done).
            do 4 rewrite big_sepM2_sep.
            iDestruct "Hkeys_disj" as "(Hkeys_disj & Hkeys_seen)"; iFrame.
            iDestruct "Hkeys" as "[(%Hfalse & _) | (_ & Hkeys)]"; first set_solver.
            iFrame.
            iDestruct (big_sepM2_sepM_2 with "[$Hkeys_hist][$Hkeys_conn_lin_hist]") as "Hkeys_hist_cm"; first done.
            iApply (big_sepM2_wand with "[$Hkeys_hist_cm]").
            iApply big_sepM2_intro.
            {
              intros k; split; intros His_some'.
              all : rewrite -elem_of_dom.
              all : rewrite -elem_of_dom in His_some'.
              all : set_solver.
            }
            iModIntro.
            iIntros (k h (p1, p2) Hlookup_m Hlookup_mc) "(Hhist_h & Hhist_cm)".
            iIntros (v Hcm_event).
            destruct p2; destruct p1 as [v'|]; simpl in Hcm_event.
            2, 3, 4 : by iApply ("Hhist_h" $! v).
            rewrite elem_of_app in Hcm_event.
            destruct Hcm_event as [Hcm_event|Hcm_event]; first by iApply ("Hhist_h" $! v).
            iApply ("Hhist_cm" $! v).
            iPureIntro; set_solver.
          + iRight.
            do 2 (iSplit; first done).
            do 4 rewrite big_sepM_sep.
            iDestruct "Hkeys_disj" as "(Hkeys_disj & Hkeys_seen)"; iFrame "∗#".
            iDestruct "Hkeys" as "[(_ & Hkeys) | (%Hfalse & _)]"; first iFrame.
            set_solver.
      }
      iModIntro.
      rewrite /commit_post_emit_event.
      wp_pures.
      wp_bind (Emit _).
      iInv "HinvExt" as ">[%T'' [%exec'' (Hinv_si_res'' & [%t'' [%lt'' 
        (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
        %Hvalid_seq'' & %Hbased'' & %Hvalid_exec'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
      iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
        as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
      assert ((#tag1, (c, (#"CmLin", #b)))%V ∈ lt'') as HstLinIn.
      {
        apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V])); last done.
        set_solver.
      }
      wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
      {
        rewrite Hkvs_inv_name.
        solve_ndisj.
      }
      {
        eapply valid_trace_post; 
        rewrite /is_post_event /is_cm_post_event;
        set_solver.
      }
      iIntros "Htr_is''".
      iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"CmPost", #b)))%V with "[$Hlin_res'']") as "Hlin_res''".
      iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"CmPost", #b)))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
      as "Hpost_res''".
      {
        simpl.
        iSplitL; first by iPureIntro.
        iPureIntro.
        rewrite /is_post_event /is_cm_post_event.
        set_solver.
      }
      iMod ("Hclose''" with "[Hinv_si_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
      {
        iModIntro.
        iExists T'', exec''.
        iFrame.
        iExists (t'' ++ [(#tag1, (c, (#"CmPost", #b)))%V]), lt''.
        iFrame.
        iSplitR; last set_solver.
        iPureIntro.
        apply (lin_trace_valid tag1); try done.
        rewrite /is_post_event /is_cm_post_event.
        set_solver.
      }
      iModIntro.
      by wp_pures.
    
    
    
    
    
    
    
    - admit.
    (* - iAssert 
      (⌜b = true⌝ ∗
        ([∗ map] k↦V;vo ∈ m;mc, k ↦ₖ commit_event vo V ∗
          (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
          (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)) ∨ 
       ⌜b = false⌝ ∗
        ([∗ map] k↦V ∈ m, k ↦ₖ V ∗
          (∀ v, ⌜v ∈ V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
          (∀ v, ⌜v ∈ V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)))%I
      with "[Hkeys1_disj Hkeys2 Hkeys3]" as "Hkeys_disj".
      {
        iDestruct "Hkeys1_disj" as "[(-> & Hkeys1)|(-> & Hkeys1)]".
        - iLeft.
          iSplit; first done.
          do 2 rewrite big_sepM2_sep.
          iFrame.
          iAssert ([∗ map] k↦ov ∈ mc, ⌜∀ v, ov = Some v → false⌝)%I as "#Hcm_sep_in'".
          {
            iApply (big_sepM_wand with "[$Hcm_sep_in]").
            iApply big_sepM_intro.
            iModIntro.
            iIntros (k ov Hlookup Himp).
            iPureIntro.
            intros v Heq.
            apply Hdec.
            destruct (Himp v Heq) as (trans & Hopen & _).
            exists trans.
            rewrite /open_trans /is_cm_op in Hopen.
            rewrite /isCmOp.
            destruct Hopen as (op & Htrans_in & Hlast & Hconn & Hcm).
            split; first done. 
            exists op.
            split_and!; try done; last (destruct op; set_solver).
            by apply last_Some_elem_of.
          }
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys2][$Hcm_sep_in']") as "Hkeys2"; first done.
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys3][$Hcm_sep_in']") as "Hkeys3"; first done.
          iSplitL "Hkeys2".
          + iApply (big_sepM2_wand with "[$Hkeys2]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hsub & %Hfalse)".
            destruct ov; set_solver.
          + iApply (big_sepM2_wand with "[$Hkeys3]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hwr & %Hfalse)".
            destruct ov; set_solver.
        - iRight.
          iSplit; first done.
          do 2 (rewrite big_sepM_sep; iFrame).
      }
      iMod (inv_ext_rc_cm_imp2 with "[$Htrans_res']") as "Htrans_res'".
      iMod ("Hclose'" with "[Htrans_res' Htr_is' HOwnLin' Hpost_res' Hlin_res' Htrace_res Hkeys_conn2 Hmap_mname
        Hmap_m Hdisj_trace_res Hmap_mstate]").
      {
        iModIntro.
        destruct (optional_applied_transaction_exists exec' [Cm (tag1, c) b]) as (st & Happl).
        iExists (T' ++ [[Cm (tag1, c) b]]), (optionalExtendExecution exec' [Cm (tag1, c) b] st).
        iFrame.
        iExists t', (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]).
        iFrame.
        iSplit; first done. 
        iSplit; first (iPureIntro; set_solver).
        iSplit; first (iPureIntro; by apply extraction_of_add1).
        iSplit.
        - iPureIntro.
          apply (valid_transactions_add1 T' (Cm (tag1, c) b) c); try done.
          + by eapply extraction_of_not_in.
          + apply valid_transaction_singleton.
          + intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
            apply Hdec.
            exists t''.
            split; first done.
            exists op.
            split_and!; try done.
            rewrite /is_cm_op in Hop_cm.
            destruct op; try done.
            exfalso.
            eauto.
         - iSplit; first done.
           iSplit; first (iPureIntro; apply based_on_add3; set_solver).
           iSplit.
           + iPureIntro.
             destruct b; last done.
             assert ([Cm (tag1, c) true] = [] ++ [Cm (tag1, c) true]) as ->; first set_solver.
             eapply valid_execution_rc_imp; try done; last set_solver.
             simpl.
             intros Hfalse.
             apply Hnot_lin_in.
             exists (toLinEvent (Cm (tag1, c) true)).
             simpl.
             destruct Hex' as (_ & Hex' & _).
             split; last done.
             apply (Hex' [Cm (tag1, c) true] (Cm (tag1, c) true)); last set_solver.
             by apply com_trans_imp2.
            + iApply (trace_state_resources_commit_lin1 clients c tag1 lt' T' sa 
                s γ γmstate γmname extract b mc mstate mname m' with 
                "[//][//][//][//][//][//][//][][Hkeys_conn2][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
              * iPureIntro.
                destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                exists e.
                split_and!; try done.
                apply elem_of_app; eauto.
              * iApply (big_sepM_wand with "[$Hkeys_conn2]").
                iApply big_sepM_intro.
                iModIntro.
                iIntros (k ov Hlookup) "(%sa' & %γ' & Hptr' & Hextract' & Himp' & Hclients_in' & _)".
                iExists sa', γ'.
                iFrame.
      }
      iMod ("Hshift" with "[Hkeys_disj Hstate_pr Hstate]"); first iFrame.
      iModIntro.
      rewrite /commit_post_emit_event.
      wp_pures.
      wp_bind (Emit _).
      iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' &  [%t'' [%lt'' 
        (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
        %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
      iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
        as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
      assert ((#tag1, (c, (#"CmLin", #b)))%V ∈ lt'') as HstLinIn.
      {
        apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V])); last done.
        set_solver.
      }
      wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
      {
        rewrite Hkvs_inv_name.
        solve_ndisj.
      }
      {
        eapply valid_trace_post; 
        rewrite /is_post_event /is_cm_post_event;
        set_solver.
      }
      iIntros "Htr_is''".
      iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"CmPost", #b)))%V with "[$Hlin_res'']") as "Hlin_res''".
      iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"CmPost", #b)))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
      as "Hpost_res''".
      {
        simpl.
        iSplitL; first by iPureIntro.
        iPureIntro.
        rewrite /is_post_event /is_cm_post_event.
        set_solver.
      }
      iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
      {
        iModIntro.
        iExists T'', exec''.
        iFrame.
        iExists (t'' ++ [(#tag1, (c, (#"CmPost", #b)))%V]), lt''.
        iFrame.
        iSplitR; last set_solver.
        iPureIntro.
        apply (lin_trace_valid tag1); try done.
        rewrite /is_post_event /is_cm_post_event.
        set_solver.
      }
      iModIntro.
      by wp_pures. *)
  Admitted.

  Lemma read_implication γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hread".
    rewrite /read_spec.
    iModIntro.
    iIntros (c sa E k) "%Hsub %Hin (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_read /KVS_wrapped_api /wrap_read.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /read_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%exec (Hinv_si_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_rd_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"RdPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"RdPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Hinv_si_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"RdPre"))%V]), lt.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_rd_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hread"; try done.
    iClear "Hread".
    iMod "Hshift" as "(%vo & Hkey_c & Hshift)".
    iDestruct "Hkey_c" as "(Hkey_c & %sa' & %γ & %ov_last_wr & #Hsa'_pointer & %Hsa'_extract & 
      Himp & %Hsa'_in & #Hlin_hist & Hloc_k_st)".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iModIntro.
    iExists vo.
    iFrame.
    iNext.
    iIntros "Hkey_c".
    iInv "HinvExt" as ">[%T' [%exec' (Hinv_si_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"RdLin", (#k, $vo))))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"RdPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"RdPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"RdLin", (#k, $vo))))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hstate_res'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {5} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa'_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iAssert (ghost_map_elem γ k (DfracOwn 1%Qp) ov_last_wr) with "[Himp]" as "Hkey_internal"; 
      first by iApply "Himp".
    assert (KVS_keys = {[k]} ∪ (KVS_keys ∖ {[k]})) as Heq_k_keys.
    {
      apply union_difference_L.
      set_solver.
    }
    iDestruct "Htrace_res" as "(%s & %c' & %γ' & %m & %Hlookup_mstate & %Hextract & #Hsa_pointer
      & Hmap_m & Htrace_res)".
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa'_pointer][$Hsa_pointer]").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(_ & _ & _ & Hfalse)|Htrace_res])".
    {
      rewrite {2} Heq_k_keys.
      rewrite (big_sepS_union _ {[k]} (KVS_keys ∖ {[k]})); last set_solver.
      rewrite big_sepS_singleton.
      iDestruct "Hfalse" as "((%ov' & Hfalse) & _)".
      iCombine "Hkey_internal" "Hfalse" as "Hfalse".
      iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
      by rewrite dfrac_valid_own in Hfalse.
    }
    iAssert (((∀ v, ⌜ov_last_wr = Some v⌝ → ⌜ov_last_wr = vo ∧ ∃ t' s', t' ∈ T' ∧ Wr s' k v ∈ t'⌝) ∗
             ⌜latest_write c k ov_last_wr T'⌝)%I) 
            as "(%Hread_res_1 & %Hread_res_2)".
    {
      iDestruct (@ghost_map_lookup with "[$Hmap_m][$Hkey_internal]") as "%Hlookup_m".
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & %Hopen_tail &
          Hkeys & Hkey_info)".
      destruct (decide (k ∈ domain ∩ KVS_keys)) as [Hk_in_dom|Hk_nin_dom].
      - iAssert (⌜latest_write c k ov_last_wr T'⌝%I) as "%Hlatest_write"; 
            first iApply "Hkey_info"; try done.
        iSplit; last iPureIntro; last eauto.
        iIntros (v' Heq_some).
        iDestruct ("Hloc_k_st" with "[//]") as "(%γm_conn & %γsnap & _ & 
          [(%Hfalse & _)|(%v'' & %Heq_ov_last_wr & _)])"; first set_solver.
        iPureIntro.
        split; first set_solver.
        inversion Heq_some as [Heq_v_v'].
        rewrite Heq_v_v' in Hlatest_write.
        destruct Hlatest_write as [Hfalse | 
          (v & t_wr & s & Heq_some' & (_ & Ht_wr_in & _) & Hwr_in & _)];
          set_solver.
      - assert ((KVS_keys ∖ (domain ∩ KVS_keys)) = 
            {[k]} ∪ ((KVS_keys ∖ (domain ∩ KVS_keys)) ∖ {[k]})) as Heq_k_keys'.
        {
          apply union_difference_L.
          set_solver.
        }
        rewrite Heq_k_keys'.
        rewrite (big_sepS_union _ {[k]} ((KVS_keys ∖ (domain ∩ KVS_keys)) ∖ {[k]})); 
          last set_solver.
        iDestruct "Hkeys" as "(Hkeys_k & _)".
        rewrite big_sepS_singleton.
        iDestruct "Hkeys_k" as "(%ov & Hkeys_k)".
        iCombine "Hkeys_k" "Hkey_internal" as "Hfalse".
        iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
        by rewrite dfrac_valid_own in Hfalse.
    }
    iAssert (∀ v, ⌜vo = Some v⌝ → ⌜∃ s t, t ∈ T' ∧ (Wr s k v) ∈ t⌝)%I as "%Hread_res_3".
    {
      iIntros (v ->).
      iDestruct ("Hlin_hist" $! v with "[//]") as "(%lh & %tag_wr & %c_wr & #HOwnLinHist_wr & %Hwr_in)".
      iDestruct (own_lin_prefix with "[$HOwnLin' $HOwnLinHist_wr]") as "(_ & _ & %Hprefix')".
      assert ((#tag_wr, (c_wr, (#"WrLin", (#k, v))))%V ∈ (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ (Some v)))))%V])) 
        as HwrLinIn; first by apply (elem_of_prefix lh).
      rewrite elem_of_app in HwrLinIn.
      destruct HwrLinIn as [HwrLinIn|HwrLinIn]; last set_solver.
      destruct Hex' as (Hex' & _).
      iPureIntro.
      specialize (Hex' (#tag_wr, (c_wr, (#"WrLin", (#k, v))))%V (Wr (tag_wr, c_wr) k v) HwrLinIn).
      exists (tag_wr, c_wr).
      apply Hex'.
      by simpl.
    }
    iDestruct "Hinv_si_res'" as "(%mnames & Hmap_mnames & %m_gl & Hmap_m_gl & Hkey_some_m_gl & Hown_exec & 
      %Hrel_exec & Hopen_trans_state)".
    rewrite /open_transactions_state.
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hopen_trans_state" as "(Hopen_trans_state_sa & Hopen_trans_state)".
    rewrite big_sepS_singleton.
    iDestruct "Hpers_pointer" as "(%γ' & (_ & (%γm_conn' & %γsnap' & #Hpers_pointer)))".
    iDestruct (@ghost_map_lookup with "[$Hmap_mnames][$Hpers_pointer]") as "%Hlookup_mnames".
    iDestruct "Hopen_trans_state_sa" as "[%Hfalse|(%c_sa & %m_conn_sa & %γm_conn_sa & %γsnap_sa & %H_sa_names & 
      Hmap_m_conn_half & %Htrans_reads)]"; first set_solver.
    iAssert (⌜c = c_sa⌝)%I as "<-"; first set_solver.
    iAssert ((⌜ov_last_wr = None⌝ → ⌜m_conn_sa !! k = Some vo⌝)%I) as "%Hread_res_4".
    {
      iIntros (->).
      iDestruct ("Hloc_k_st" with "[//]") as "(%γm_conn & %γupd_st & #Hsa_pointer' & 
        [(_ & Hkey_m_conn)|(%v'' & %Hfalse & _)])"; 
        last (inversion Hfalse; set_solver).
      iDestruct (@ghost_map_lookup with "[$Hmap_mnames][$Hsa_pointer']") as "%Hlookup_mnames'".
      assert (γm_conn = γm_conn_sa) as <-; first set_solver.
      by iDestruct (@ghost_map_lookup with "[$Hmap_m_conn_half][$Hkey_m_conn]") as "%Hlookup_m_conn".
    }
    iMod ("Hclose'" with "[Hmap_mnames Hmap_m_gl Hkey_some_m_gl Hown_exec Hopen_trans_state Hmap_m_conn_half
      Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res HOwnLin' Hpost_res' Hlin_res']").
    {
      iNext.
      assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as Hdecision.
      {
        do 2 (apply list_exist_dec; intros).
        apply _.
      }
      assert (lin_trace_of (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ vo))))%V]) t') as Hlin_of_add.
      {
        apply (lin_trace_lin lt' (#tag1, (c, #"RdPre"))%V
          (#tag1, (c, (#"RdLin", (#k, $ vo))))%V tag1 c t'); try done;
          rewrite /is_lin_event /is_rd_lin_event /is_pre_event /is_rd_pre_event;
          destruct vo; set_solver.
      }
      iAssert (⌜valid_sequence (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ vo))))%V])⌝)%I as "%Hvalid_seq_add".
      {
        iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & %Hopen_start & Hrest)".
        iPureIntro.
        apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
        - right.
          rewrite /is_rd_lin_event.
          destruct vo; set_solver.
        - by exists t'.
        - intros tag' c' k' v' Heq.
          inversion Heq.
          destruct vo as [v|]; last done.
          subst.
          assert (v = v') as <-; first set_solver.
          destruct Hex' as (_ & Hex' & _).
          destruct (Hread_res_3 v) as (s1 & t1 & Ht1_in & Hwr_in); first done.
          specialize (Hex' t1 (Wr s1 k v) Ht1_in Hwr_in).
          destruct s1; simpl in Hex'; eauto.
      }
      destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
          as [(trans & Htrans_in & Hop)|Hdec].
      - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
        iExists (T1 ++ (trans ++ [Rd (tag1, c) k vo]) :: T2), exec'.
        assert (valid_transactions (T1 ++ (trans ++ [Rd (tag1, c) k vo]) :: T2)) as Hvalid_trans_add.
        {
          apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
          - by eapply extraction_of_not_in.
          - by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
          - intros s' k' ov' tag' v' Heq Hin_wr Hnot.
            destruct (decide (ov' = Some v')) as [Heq'|Hneq']; first done.
            exfalso.
            apply Hnot.
            assert (k = k') as <-; first set_solver.
            destruct (ov_last_wr) as [v_last|] eqn:Heq_ov_last_wr. 
            + destruct Hread_res_2 as [Hfalse| (v'' & trans' & tag_wr & Heq_some' & Hopen_trans & Hwr_in & Hrel)]; 
                first set_solver.
              assert (v_last  = v'') as <-; first set_solver.
              exists tag_wr, v_last.
              assert (trans = trans') as <-; first by eapply trans_eq.
              rewrite elem_of_list_lookup in Hwr_in.
              destruct Hwr_in as (i & Hwr_in).
              split; first (apply rel_list_imp; set_solver).
              assert (i < length trans) as Hlength; 
                first by eapply lookup_lt_Some.
              rewrite /rel_list.
              exists i, (length trans).
              split_and!; try done; 
                first by apply lookup_app_l_Some.
              assert (Init.Nat.pred (length (trans ++ [Rd (tag1, c) k vo])) = 
                length trans) as <-; last by rewrite -last_lookup last_snoc.
               rewrite last_length; lia.
            + destruct Hread_res_2 as [(_ & Hread_res_2)|Hfalse]; last set_solver.
              exfalso.
              apply (Hread_res_2 trans); last eauto.
              destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
              exists op.
              rewrite /is_cm_op.
              split_and!; try done.
              destruct op; simpl in Hop_cm; set_solver.
          - destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
            exists op.
            split_and!; try done.
            intros (s' & b' & ->).
            set_solver.
        }
        iSplitL "Hmap_mnames Hmap_m_gl Hkey_some_m_gl Hown_exec Hopen_trans_state Hmap_m_conn_half".
        {
          iExists mnames; iFrame.
          iExists m_gl; iFrame.
          iSplit; first done.
          rewrite /open_transactions_state.
          rewrite {4} Heq_sa_clients.
          rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
          iSplitR "Hopen_trans_state".
          - rewrite big_sepS_singleton.
            iRight.
            iExists c, m_conn_sa, γm_conn_sa, γsnap_sa.
            iSplit; first done.
            iFrame.
            iPureIntro.
            intros trans' Hopen_trans'.
            assert ((trans ++ [Rd (tag1, c) k vo]) = trans') as <-; first eapply trans_eq; try done.
            {
              exists (Rd (tag1, c) k vo); simpl.
              split_and!; try done; first set_solver.
              apply last_snoc.
            }
            assert (open_trans trans c (T1 ++ trans :: T2)) as Hopen_trans.
            {
              destruct Hop as (op & Hop).
              exists op.
              split; first set_solver.
              do 2 (split; first set_solver).
              rewrite /is_cm_op.
              destruct op; simpl in Hop; set_solver.
            }
            destruct (Htrans_reads trans Hopen_trans) as (Htrans_reads_1 & Htrans_reads_2).
            split.
            {
              intros sig k' ov v' [Hop_in|Hop_in]; rewrite elem_of_app in Hop_in.
              - destruct Hop_in as [Hfalse|Hop_in]; last set_solver.
                eapply Htrans_reads_1; left; set_solver.
              - destruct Hop_in as [Hop_in|Hop_in].
                + eapply Htrans_reads_1; right; set_solver.
                + assert (k' = k) as ->; set_solver.
            }
            intros sig k' ov' Hrd_in Hnot.
            rewrite elem_of_app in Hrd_in.
            destruct Hrd_in as [Hrd_in|Hrd_in].
            + apply (Htrans_reads_2 sig k' ov' Hrd_in).
              intros (sig' & v' & Hrel).
              apply Hnot.
              exists sig', v'.
              by apply rel_list_imp.
            + destruct (ov_last_wr) as [v_last|] eqn:Heq_ov_last_wr; last set_solver.
              exfalso.
              apply Hnot.
              destruct Hread_res_2 as [Hfalse | (v & t_wr & s' & Heq_some' & Hopen_trans'' & Hwr_in & _)];
                first set_solver.
              exists (s', c), v.
              assert (trans = t_wr) as <-; first by eapply trans_eq.
              apply elem_of_list_lookup in Hwr_in.
              destruct Hwr_in  as (i & Hwr_in).
              exists i, (Init.Nat.pred (length (trans ++ [Rd (tag1, c) k vo]))).
              split_and!.
              * rewrite app_length; simpl.
                apply lookup_lt_Some in Hwr_in.
                lia.
              * apply lookup_app_l_Some; set_solver.
              * rewrite -last_lookup last_snoc.
                set_solver.
          - iApply (big_sepS_wand with "[$Hopen_trans_state]").
            iApply big_sepS_intro.
            iModIntro.
            iIntros (sa'' Hsa''_in).
            iIntros "[Hopen_state_sa|(%c'' & %m_conn'' & %γm_conn'' & %γsnap'' & 
              (%Hextract'' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
            iRight.
            iExists c'', m_conn'', γm_conn'', γsnap''.
            iSplit; first done.
            iFrame.
            iPureIntro.
            intros trans' Hopen.
            assert (open_trans trans' c'' (T1 ++ trans :: T2)) as Hopen'.
            {
              eapply (open_trans_neq3 _ sa sa'' c c'' _ _ _ _ (Rd (tag1, c) k vo)); 
                rewrite /connOfOp; set_solver.
            }
            specialize (Hopen_state trans' Hopen').
            set_solver.
            Unshelve.
            all : done.
        }
        iExists t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ vo))))%V]).
        iFrame.
        iSplit; first done.
        iSplit; first (iPureIntro; by apply trans_add_non_empty).
        iSplit; first (iPureIntro; destruct vo; by apply extraction_of_add2).
        do 2 (iSplit; first done).
        iSplit; first by (iPureIntro; eapply based_on_add1; rewrite /is_cm_op; set_solver).
        iSplit; first by simpl.
        iApply (trace_state_resources_read_lin2 clients c tag1 lt' T1 T2 trans k sa vo
          s γ γmstate γmname extract mstate mname m with "[][][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
          [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
        + iPureIntro.
          intros Hfalse.
          eapply two_trans_implies_false_app_cons; try done.
          exists (Rd (tag1, c) k vo); simpl.
          split_and!; try done; first set_solver.
          apply last_snoc.
        + iPureIntro.
          destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try done.
          apply elem_of_app; eauto.
      - iExists (T' ++ [[Rd (tag1, c) k vo]]), exec'.
        assert (valid_transactions (T' ++ [[Rd (tag1, c) k vo]])) as Hvalid_trans_add.
        {
          apply (valid_transactions_add1 T' (Rd (tag1, c) k vo) c); try done.
          - by eapply extraction_of_not_in.
          - set_solver.
          - apply valid_transaction_singleton.
          - intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
            apply Hdec.
            exists t''.
            split; first done.
            exists op.
            split_and!; try done.
            rewrite /is_cm_op in Hop_cm.
            destruct op; try done.
            exfalso.
            eauto.
        }
        iSplitL "Hmap_mnames Hmap_m_gl Hkey_some_m_gl Hown_exec Hopen_trans_state Hmap_m_conn_half".
        {
          iExists mnames; iFrame.
          iExists m_gl; iFrame.
          iSplit; first done.
          rewrite /open_transactions_state.
          rewrite {4} Heq_sa_clients.
          rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
          iSplitR "Hopen_trans_state".
          - rewrite big_sepS_singleton.
            iRight.
            iExists c, m_conn_sa, γm_conn_sa, γsnap_sa.
            iSplit; first done.
            iFrame.
            iPureIntro.
            intros trans' Hopen_trans'.
            assert ([Rd (tag1, c) k vo] = trans') as <-; first eapply trans_eq; try done.
            {
              exists (Rd (tag1, c) k vo); simpl.
              split_and!; try done; first set_solver.
            }
            split.
            {
             intros s' k' ov' v' [Hin''|Hin'']; first set_solver.
             assert (k = k') as ->; set_solver. 
            }
            intros sig k' ov' Hrd_in Hnot.
            destruct (ov_last_wr) as [v_last|] eqn:Heq_ov_last_wr; last set_solver.
            exfalso.
            apply Hdec.
            destruct Hread_res_2 as [Hfalse | (v & t_wr & s' & Heq_some' & Hopen_trans'' & Hwr_in & _)];
              first set_solver.
            exists t_wr.
            destruct Hopen_trans'' as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
            split; first done.
            exists op.
            split_and!; try done.
            + by apply last_Some_elem_of.
            + rewrite /is_cm_op in Hop_cm.
              destruct op; try done.
              exfalso.
              eauto.
          - iApply (big_sepS_wand with "[$Hopen_trans_state]").
            iApply big_sepS_intro.
            iModIntro.
            iIntros (sa'' Hsa''_in).
            iIntros "[Hopen_state_sa|(%c'' & %m_conn'' & %γm_conn'' & %γsnap'' & 
              (%Hextract'' & %Hnames_lookup) & Hmap_mconn & %Hopen_state)]"; first by iLeft.
            iRight.
            iExists c'', m_conn'', γm_conn'', γsnap''.
            iSplit; first done.
            iFrame.
            iPureIntro.
            intros trans Hopen.
            assert (open_trans trans c'' T') as Hopen'.
            {
              rewrite /open_trans in Hopen.
              rewrite /open_trans.
              set_solver.
            }
            specialize (Hopen_state trans Hopen').
            set_solver.
        }
        iExists t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ vo))))%V]).
        iFrame.
        iSplit; first done.
        iSplit; first (iPureIntro; set_solver).
        iSplit; first (iPureIntro; destruct vo; by apply extraction_of_add1).
        iSplit.
        + iPureIntro.
          apply (valid_transactions_add1 T' (Rd (tag1, c) k vo) c); try done.
          * by eapply extraction_of_not_in.
          * set_solver.
          * apply valid_transaction_singleton.
          * intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
            apply Hdec.
            exists t''.
            split; first done.
            exists op.
            split_and!; try done.
            rewrite /is_cm_op in Hop_cm.
            destruct op; try done.
            exfalso.
            eauto.
        + iSplit; first done.
          iSplit; first (iPureIntro; apply based_on_add2; rewrite /is_cm_op; set_solver).
          iSplit; first by simpl.
          iApply (trace_state_resources_read_lin1 clients c tag1 lt' T' k sa vo
            s γ γmstate γmname extract mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
            [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
          iPureIntro.
          destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try done.
          apply elem_of_app; eauto.
    }
    iMod ("Hshift" with "[Hkey_internal Hkey_c Hloc_k_st]").
    {
      simpl.
      iFrame.
      iExists sa, γ, ov_last_wr.
      iFrame "#".
      iSplit; first done.
      iSplitL "Hkey_internal"; first (iIntros (_); iFrame).
      iSplit; first done.
      iIntros (_).
      by iApply "Hloc_k_st".
    }
    iModIntro.
    rewrite /read_post_emit_event.
    wp_pures.
    wp_bind (Emit _).
    iInv "HinvExt" as ">[%T'' [%exec'' (Hinv_si_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & %Hbased'' & %Hvalid_exec'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, (#"RdLin", (#k, $ vo))))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ vo))))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; try done; destruct vo;
        rewrite /is_post_event /is_rd_post_event;
        set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"RdPost", (#k, $vo))))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"RdPost", (#k, $vo))))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      destruct vo;
      rewrite /is_post_event /is_rd_post_event;
      set_solver.
    }
    iMod ("Hclose''" with "[Hinv_si_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [_]), lt''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      destruct vo;
      rewrite /is_post_event /is_rd_post_event;
      set_solver.
    }
    iModIntro.
    wp_pures.
    destruct vo; simpl; iFrame.
  Qed.

  Lemma write_implication γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hwrite".
    rewrite /write_spec.
    iModIntro.
    iIntros (c sa E k v) "%Hsub %Hin (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_write /KVS_wrapped_api /wrap_write.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /write_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%exec (Hinv_si_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_wr_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"WrPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"WrPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Hinv_si_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"WrPre"))%V]), lt.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_wr_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hwrite"; try done.
    iClear "Hwrite".
    iMod "Hshift" as "(%vo & %b & (Hkey_c & Hkey_upd) & Hshift)".
    iDestruct "Hkey_c" as "(Hkey_c & (%sa' & %γ & %ov_last_wr & #Hsa'_pointer & %Hsa'_extract & 
      Himp & %Hsa'_in & #Hlin_hist & Hkey_loc_st))".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iDestruct "Hkey_upd" as "(Hkey_upd & %sa'' & %γm_conn & %γsnap & %Hsa''_extract & 
      #Hsa''_pointer_si & Hkey_upd_disj)".
    destruct (decide (sa = sa'')) as [<- | Hfalse]; last set_solver.
    iModIntro.
    iExists vo, b.
    iFrame.
    iNext.
    iIntros "Hkey_c".
    iInv "HinvExt" as ">[%T' [%exec' (Hinv_si_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"WrLin", (#k, v))))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"WrPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"WrPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"WrLin", (#k, v))))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hstate_res'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {6} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa'_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iAssert (ghost_map_elem γ k (DfracOwn 1%Qp) ov_last_wr) with "[Himp]" as "Hkey_internal"; 
      first by iApply "Himp".
    assert (KVS_keys = {[k]} ∪ (KVS_keys ∖ {[k]})) as Heq_k_keys.
    {
      apply union_difference_L.
      set_solver.
    }
    iDestruct "Htrace_res" as "(%s & %c' & %γ' & %m & %Hlookup_mstate & %Hextract & #Hsa_pointer
      & Hmap_m & Htrace_res)".
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa'_pointer][$Hsa_pointer]").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(_ & _ & Hfalse)|Htrace_res])".
    {
      rewrite {3} Heq_k_keys.
      rewrite (big_sepS_union _ {[k]} (KVS_keys ∖ {[k]})); last set_solver.
      rewrite big_sepS_singleton.
      iDestruct "Hfalse" as "(_ & (%ov' & Hfalse) & _)".
      iCombine "Hkey_internal" "Hfalse" as "Hfalse".
      iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
      by rewrite dfrac_valid_own in Hfalse.
    }
    iMod (@ghost_map_update _ Key (option val) _ _ _ _ _ k ov_last_wr (Some v.(SV_val)) with "[$Hmap_m] [$Hkey_internal]") 
      as "(Hmap_m & Hkey_internal)".
    iMod ("Hclose'" with "[Hinv_si_res' Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res 
      HOwnLin' Hpost_res' Hlin_res']").
    {
      iNext.
      assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as Hdecision.
      {
        do 2 (apply list_exist_dec; intros).
        apply _.
      }
      assert (lin_trace_of (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]) t') as Hlin_of_add.
      {
        apply (lin_trace_lin lt' (#tag1, (c, #"WrPre"))%V 
            (#tag1, (c, (#"WrLin", (#k, v))))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_wr_lin_event /is_pre_event /is_wr_pre_event; 
            do 2 right; left; eauto.
      }
      iAssert (⌜valid_sequence (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V])⌝)%I as "%Hvalid_seq_add".
      {
        iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & %Hopen_start & Hrest)".
        iPureIntro.
        apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done; last by exists t'.
        rewrite /is_wr_lin_event; set_solver.
      }
      destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
          as [(trans & Htrans_in & Hop)|Hdec].
      - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
        iExists (T1 ++ (trans ++ [Wr (tag1, c) k v]) :: T2), exec'.
        assert (valid_transactions (T1 ++ (trans ++ [Wr (tag1, c) k v]) :: T2)) as Hvalid_added.
        {
          apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
          - by eapply extraction_of_not_in.
          - by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
          - destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
            exists op.
            split_and!; try done.
            intros (s' & b' & ->).
            set_solver.
        }
        iSplitL "Hinv_si_res'"; first (by iApply inv_ext_si_wr_imp1).
        iExists t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]).
        iFrame.
        iSplit; first done.
        iSplit; first (iPureIntro; by apply trans_add_non_empty).
        iSplit; first (iPureIntro; by apply extraction_of_add2).
        do 2 (iSplit; first done).
        iSplit; first (iPureIntro; eapply based_on_add1; rewrite /is_cm_op; set_solver).
        iSplit; first by simpl.
        iApply (trace_state_resources_write_lin2 clients c tag1 lt' T1 T2 trans k v sa 
          s γ γmstate γmname extract mstate mname m with "[][][][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
          [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
        + iPureIntro.
          intros Hfalse.
          eapply two_trans_implies_false_app_cons; try done.
          exists (Wr (tag1, c) k v); simpl.
          rewrite last_snoc; set_solver.
        + iPureIntro.
          destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try done.
          apply elem_of_app; eauto.
      - iExists (T' ++ [[Wr (tag1, c) k v]]), exec'.
        assert (valid_transactions (T' ++ [[Wr (tag1, c) k v]])) as Hvalid_added.
        {
          apply (valid_transactions_add1 T' (Wr (tag1, c) k v) c); try done.
          - by eapply extraction_of_not_in.
          - apply valid_transaction_singleton.
          - intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
            apply Hdec.
            exists t''.
            split; first done.
            exists op.
            split_and!; try done.
            rewrite /is_cm_op in Hop_cm.
            destruct op; try done.
            exfalso.
            eauto.
        }
        iSplitL "Hinv_si_res'"; first (by iApply inv_ext_si_wr_imp2).
        iExists t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]).
        iFrame.
        iSplit; first done.
        iSplit; first (iPureIntro; set_solver).
        iSplit; first (iPureIntro; by apply extraction_of_add1).
         do 2 (iSplit; first done).
        iSplit; first (iPureIntro; apply based_on_add2; rewrite /is_cm_op; set_solver).
        iSplit; first by simpl.
        iApply (trace_state_resources_write_lin1 clients c tag1 lt' T' k v.(SV_val) sa
          s γ γmstate γmname extract mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
          [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
        iPureIntro.
        destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
        exists e.
        split_and!; try done.
        apply elem_of_app; eauto.
    }
    iMod ("Hshift" with "[Hkey_loc_st Hkey_internal Hkey_c Hkey_upd_disj]").
    {
      iDestruct "Hkey_c" as "(Hkey_c & Hkey_upd)".
      iAssert (ghost_map_elem γsnap k (DfracOwn 1%Qp) None ∗ ∃ (ov : option val), ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov)%I 
        with "[Hkey_loc_st Hkey_upd_disj]" as "(Hkey_upd_snap & (%ov' & Hkey_conn))".
      {
        iDestruct ("Hkey_loc_st" with "[//]") as "(%γm_conn' & %γsnap' & #Hsa_pointer_si & Hdisj)".
        iDestruct (ghost_map_elem_agree sa γsi_name _ _ (Some (γm_conn, γsnap, c)) 
          (Some (γm_conn', γsnap', c)) with "[$Hsa''_pointer_si][$Hsa_pointer_si]") as "%Heq_names".
        assert (γsnap'= γsnap) as ->; first set_solver.
        assert (γm_conn'= γm_conn) as ->; first set_solver.
        destruct (b).
        - iDestruct ("Hkey_upd_disj" with "[//]") as "[(_ & (%ov' & Hkey_conn))|(%Hfalse & _)]"; last set_solver.
          iDestruct "Hdisj" as "[(_ & Hfalse)|(%v' & _ & Hkey_upd_snap)]"; last (iFrame; eauto).
          iDestruct (ghost_map_elem_valid_2 with "Hfalse Hkey_conn") as %[Hfalse _].
          exfalso; set_solver.
        - iDestruct ("Hkey_upd_disj" with "[//]") as "[(%Hfalse & _)|(_ & Hkey_upd_snap)]"; first set_solver.
          iDestruct "Hdisj" as "[(_ & Hkey_conn)|(%v' & _ & Hfalse)]"; first (iFrame; eauto).
          iDestruct (ghost_map_elem_valid_2 with "Hfalse Hkey_upd_snap") as %[Hfalse _].
          exfalso; set_solver.
      }
      simpl.
      iSplitL "Hkey_c Hkey_internal Hkey_upd_snap"; iFrame.
      - iExists sa, γ, (Some v.(SV_val)). 
        iFrame "#".
        iSplit; first done.
        iSplitL "Hkey_internal"; first (iIntros (_); iFrame).
        iSplit; first done.
        iSplit.
        + iIntros (v' Heq_some).
          iExists (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]), tag1, c.
          iFrame "#".
          iPureIntro; set_solver.
        + iIntros (_).
          iExists γm_conn, γsnap.
          iFrame "#".
          iRight.
          iFrame.
          eauto.
      - iExists sa, γm_conn, γsnap.
        iSplit; first done.
        iFrame "#".
        eauto.
    }
    iModIntro.
    rewrite /write_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%exec'' (Hinv_si_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & %Hbased'' & %Hvalid_exec'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, (#"WrLin", (#k, v))))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; 
      rewrite /is_post_event /is_wr_post_event;
      set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"WrPost", (#k, v))))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"WrPost", (#k, v))))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    iMod ("Hclose''" with "[Hinv_si_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [(#tag1, (c, (#"WrPost", (#k, v))))%V]), lt''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma start_implication γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hstart".
    rewrite /start_spec.
    iModIntro.
    iIntros (c sa E) "%Hsub (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_start /KVS_wrapped_api /wrap_start.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /start_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%exec (Hinv_si_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_st_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"StPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"StPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Hinv_si_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"StPre"))%V]), lt.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_st_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hstart"; try done.
    iClear "Hstart".
    iMod "Hshift" as "[%m (((Hconn_state & %γm_conn & %γsnap & %m_conn & #Hsa_pointer_si & Hghost_map_m_conn &
      Hconn_exec_state) & Hkeys) & Hshift)]".
    iDestruct "Hconn_exec_state" as "[(_ & Hsa_pointer & Hkeys_conn_si)|(%ms & %ms_sub & %Hfalse & _)]"; 
      last (exfalso; set_solver).
    iModIntro.
    iExists m.
    iFrame.
    simpl.
    rewrite {1} big_sepM_sep.
    iDestruct "Hkeys" as "(Hkeys1 & Hkeys2)".
    iFrame.
    iModIntro.
    iIntros "(Hconn_state & Hkeys1 & Hkeys_conn & #Hseen)".
    rewrite (big_sepM_sep _ (λ k _,  KeyUpdStatus c k false) m).
    iDestruct "Hkeys_conn" as "(Hkeys_conn & Hkeys_status)".
    iInv "HinvExt" as ">[%T' [%exec' (Hinv_si_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
    simpl.
    iDestruct "Hstate_res'" as "(%mstate' & Hghost_map_mstate' & %mname' & Hghost_map_mname' & Hdisj_trace_res)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mstate'][$Hsa_pointer]") as "%Hlookup_mstate'".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {5} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct "Hdisj_trace_res_sa" as "[(Hfalse & _) | Htrace_res]".
    {
      iDestruct "Hfalse" as "[%Hfalse | %Hfalse]"; set_solver.
    }
    iDestruct "Htrace_res" as "(%ls & %c' & %γ & %m' & %Hlookup_mstate'' & %Hextract & 
      #Hsa_c'_pointer & Hghost_map_m' & %Hinit & [(-> & %Hclosed & %Hopen_trans & Hkeys_conn_res) | Hfalse])"; last first.
    {
      assert (ls = CanStart) as ->; first set_solver.
      by iDestruct "Hfalse" as "(%domain & %sub_domain & %tail & %Hfalse & _)".
    }
    iMod (ghost_map_update (Active (dom m), Some c) with "[$Hghost_map_mstate'] [$Hsa_pointer]") 
      as "(Hghost_map_mstate' & Hsa_pointer)".
    iAssert ((|==> (([∗ set] k ∈ KVS_keys, ghost_map_elem γ k (DfracOwn 1%Qp) None) ∗ 
              (∃ m'', ghost_map_auth γ 1 m'' ∧ ⌜∀ k, k ∈ KVS_keys → m'' !! k = Some None⌝)))%I) 
      with "[Hkeys_conn_res Hghost_map_m']" as ">(Hkeys_conn_res & (%m'' & Hghost_map_m' & %Hnone))".
    {
      iRevert "Hghost_map_m'".
      iRevert (m').
      iInduction KVS_keys as [|k KVS_Keys Hnin] "IH" using set_ind_L.
      - iIntros (m') "Hghost_map_m'".
        iModIntro. 
        iSplitR "Hghost_map_m'"; first done.
        iExists m'.
        iFrame.
        iPureIntro.
        set_solver.
      - iIntros (m') "Hghost_map_m'".
        rewrite big_sepS_union; last set_solver.
        iDestruct "Hkeys_conn_res" as "(Hkeys_conn_key & Hkeys_conn_res)".
        iMod ("IH" with "[$Hkeys_conn_res][$Hghost_map_m']") 
          as "(Hkeys_conn_res & [%m'' (Hghost_map' & %Hnone)])".
        rewrite big_sepS_singleton.
        iDestruct "Hkeys_conn_key" as "(%ov & Hkeys_conn_key)".
        iMod (@ghost_map_update _ Key (option val) _ _ _ _ _ k ov None with "[$Hghost_map'] [$Hkeys_conn_key]") 
          as "(Hghost_map' & Hkeys_conn_key)".
        iModIntro.
        iSplitR "Hghost_map'".
        + rewrite big_sepS_union; last set_solver.
          iFrame. 
          rewrite big_sepS_singleton.
          iFrame.
        + iExists _.
          iFrame.
          iPureIntro.
          intros k' Hin.
          destruct (decide (k = k')) as [->|Hneq].
          * by rewrite lookup_insert.
          * rewrite lookup_insert_ne; last done.
            apply Hnone.
            set_solver.
    }
    iAssert ((([∗ set] k ∈ (dom m) ∩ KVS_keys, ghost_map_elem γ k (DfracOwn 1%Qp) None) ∗ 
              ([∗ set] k ∈ KVS_keys ∖ ((dom m) ∩ KVS_keys), ghost_map_elem γ k (DfracOwn 1%Qp) None))%I) 
      with "[Hkeys_conn_res]" as "(Hkeys_conn_res1 & Hkeys_conn_res2)".
    {
      assert (KVS_keys = (dom m ∩ KVS_keys) ∪ (KVS_keys ∖ (dom m ∩ KVS_keys))) as Heq.
      - apply union_difference_L.
        set_solver.
      - rewrite {1} Heq.
        rewrite (big_sepS_union _ (dom m ∩ KVS_keys) (KVS_keys ∖ (dom m ∩ KVS_keys))); last set_solver.
        iFrame.
    }
    iMod (own_lin_add _ _ (#tag1, (c, #"StLin"))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"StPre"))%V ∈ t') as Hin.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"StPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, #"StLin"))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hinv_si_res'" as "(%mnames_si & Hghost_map_mnames_si & %m_gl & Hghot_map_m_gl & 
      %Hkeys_some_m_gl & Hown_exec & %Hrel_exec & Hopen_trans_state)".
    iDestruct (get_obs with "Hown_exec") as "#Hown_exec_hist".
    rewrite /open_transactions_state.
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hopen_trans_state" as "(Hopen_trans_state_sa & Hopen_trans_state)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mnames_si][$Hsa_pointer_si]") as "%Hlookup'".
    iDestruct "Hopen_trans_state_sa" as "[%Hfalse|(%c_sa & %m_conn_sa' & %γ_sa & %γ''_sa & %Hextract_c_sa 
      & Hghost_map_m_conn_sa & Hopen_state)]"; first (exfalso; set_solver).
    iAssert (⌜m ⊆ m_gl⌝)%I as "%Hsubset".
    {
      iApply (@ghost_map_lookup_big with "[$Hghot_map_m_gl][Hkeys2]").
      iApply (big_sepM_wand with "[$Hkeys2]").
      iApply big_sepM_intro.
      iModIntro.
      iIntros (k h Hlookup_k) "(Hkey_res & _)".
      iFrame.
    }
    destruct Hrel_exec as (st_new & Hrel_exec).
    assert (γ_sa = γm_conn) as ->; first set_solver.
    iDestruct (@ghost_map.ghost_map_auth_agree _ Key (option val) 
      with "[$Hghost_map_m_conn][$Hghost_map_m_conn_sa]") as "<-".
    iCombine "Hghost_map_m_conn" "Hghost_map_m_conn_sa" as "Hghost_map_m_conn".
    iAssert ((|==> (([∗ set] k ∈ KVS_keys, ((∃ (ov : option val), ⌜k ∈ dom m⌝ ∗ ⌜(∃ h, m !! k = Some h ∧ last h = ov)⌝ ∗ ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov) ∨ ⌜k ∉ dom m⌝) ∗
      ghost_map_elem γsnap k (DfracOwn 1%Qp) None) ∗ 
      (∃ m_conn', ⌜∀ k, k ∉ KVS_keys → m_conn !! k = m_conn' !! k⌝ ∧ 
        ⌜∀ k, k ∈ KVS_keys → k ∉ dom m → m_conn' !! k = None⌝ ∗ ghost_map_auth γm_conn 1 m_conn' ∧ 
        ⌜∀ k ov, k ∈ KVS_keys → k ∈ dom m → (m_conn' !! k = Some ov → (∃ h, m !! k = Some h ∧ last h = ov))⌝)))%I)
      with "[Hghost_map_m_conn Hkeys_conn_si]" as ">(Hkeys_conn_si & (%m_conn' & _ & %Hm_conn'_none & Hghost_map_m_conn & %Hm_conn'_st_new_rel))".
    {
      clear Hnone Hkeys_some_m_gl Hrel_exec.
      iRevert "Hghost_map_m_conn Hkeys_conn_si".
      iRevert (m_conn).
      iInduction KVS_keys as [|k KVS_Keys Hnin] "IH" using set_ind_L.
      - iIntros (m_conn) "Hghost_map_m_conn Hkeys_conn_si".
        iModIntro.
        iSplit; first done.
        iExists m_conn.
        set_solver.
      - iIntros (m_conn) "Hghost_map_m_conn Hkeys_conn_si".
        rewrite big_sepS_union; last set_solver.
        iDestruct "Hkeys_conn_si" as "(Hkeys_conn_si_k & Hkeys_conn_si)".
        rewrite big_sepS_singleton.
        iDestruct "Hkeys_conn_si_k" as "(%ov & Hkey1 & Hkey2)".
        iMod ("IH" with "[$Hghost_map_m_conn][$Hkeys_conn_si]") as 
          "(Hkeys_conn_si & (%m_conn' & %Himp0 & %Himp1 & Hghost_map_m_conn & %Himp2))".
        destruct (m !! k) as [h|] eqn:Hlookup_k_m; last first.
        + iAssert (|==>(ghost_map_auth γm_conn 1 (delete k m_conn')))%I with "[Hkey1 Hghost_map_m_conn]" 
            as ">Hghost_map_m_conn".
          {
            iDestruct "Hkey1" as "[Hkey1|%Hkey1]".
            - iApply (@ghost_map_delete with "[$Hghost_map_m_conn][$Hkey1]").
            - iModIntro.
              assert (m_conn' !! k = None) as Hlookup_m_conn'; first by rewrite -(Himp0 k Hnin).
              by rewrite delete_notin; first iFrame.
          }
          iModIntro.
          rewrite big_sepS_union; last set_solver.
          iFrame.
          rewrite big_sepS_singleton.
          iSplitR "Hghost_map_m_conn".
          * iFrame.
            iRight; iPureIntro.
            by apply not_elem_of_dom_2.
          * iExists (delete k m_conn').
            iFrame.
            apply not_elem_of_dom_2 in Hlookup_k_m.
            iPureIntro.
            split_and!.
            -- intros k' Hn_in.
               rewrite lookup_delete_ne; set_solver.
            -- intros k' Hk_in Hnin_m.
               rewrite elem_of_union in Hk_in.
               destruct (decide (k = k')) as [<-|Hneq]; first apply lookup_delete.
               assert (k' ∈ KVS_Keys) as Hk_in'; first set_solver.
               specialize (Himp1 k' Hk_in' Hnin_m).
               rewrite lookup_delete_ne; set_solver.
            -- intros k' ov' Hk'_in Hk'_dom Hdelete_eq.
               destruct (decide (k = k')) as [<-|Hneq]; first set_solver.
               apply Himp2; try done; first set_solver.
               rewrite lookup_delete_ne in Hdelete_eq; set_solver.
        + iAssert (|==>(ghost_map_elem γm_conn k (DfracOwn 1%Qp) (last h) ∗ ghost_map_auth γm_conn 1 (<[k:=(last h)]> (delete k m_conn'))))%I 
            with "[Hkey1 Hghost_map_m_conn]" as ">(Hkey1 & Hghost_map_m_conn)".
          {
            rewrite insert_delete_insert.
            iDestruct "Hkey1" as "[Hkey1|%Hkey1]".
            - iMod (@ghost_map_update _ Key (option val) _ _ _ _ _ k ov (last h) 
                with "[$Hghost_map_m_conn] [$Hkey1]") as "(Hghost_map_m_conn & Hkey1)".
              by iFrame.
            - assert (m_conn' !! k = None) as Hlookup_m_conn'; first by rewrite -(Himp0 k Hnin).
              iMod (ghost_map_insert k (last h) Hlookup_m_conn' with "[$Hghost_map_m_conn]") 
                as "(Hghost_map_m_conn & Hkey)".
              by iFrame.
          }
          rewrite big_sepS_union; last set_solver.
          iFrame.
          rewrite big_sepS_singleton.
          iSplitR "Hghost_map_m_conn".
          * iFrame.
            iLeft.
            iExists (last h).
            iFrame; iPureIntro.
            split; last eauto.
            apply elem_of_dom.
            rewrite /is_Some; set_solver.
          * iExists (<[k:=last h]> (delete k m_conn')).
            iFrame.
            iModIntro.
            iPureIntro.
            split_and!.
            -- intros k' Hn_in.
               rewrite lookup_insert_ne; last set_solver.
               rewrite lookup_delete_ne; set_solver.
            -- intros k' Hk_in Hnin_m.
               rewrite elem_of_union in Hk_in.
               destruct (decide (k = k')) as [<-|Hneq].
               {
                  apply not_elem_of_dom_1 in Hnin_m.
                  set_solver.
               }
               rewrite lookup_insert_ne; last done.
               rewrite lookup_delete_ne; set_solver.
            -- intros k' ov' Hk'_in Hk'_dom Hdelete_eq.
               destruct (decide (k = k')) as [<-|Hneq]. 
               {
                 rewrite lookup_insert in Hdelete_eq.
                 set_solver.
               } 
               apply Himp2; try done; first set_solver.
               rewrite lookup_insert_ne in Hdelete_eq; last done.
               rewrite lookup_delete_ne in Hdelete_eq; set_solver.
    }
    iAssert ((([∗ set] k ∈ (dom m) ∩ KVS_keys, ∃ (ov : option val), ghost_map_elem γm_conn k (DfracOwn 1%Qp) ov ∗ ⌜k ∈ dom m → (∃ h, m !! k = Some h ∧ last h = ov)⌝ ∗
      ghost_map_elem γsnap k (DfracOwn 1%Qp) None) ∗ 
      ([∗ set] k ∈ KVS_keys ∖ ((dom m) ∩ KVS_keys), ⌜m_conn' !! k = None⌝ ∗ ghost_map_elem γsnap k (DfracOwn 1%Qp) None))%I) 
      with "[Hkeys_conn_si]" as "(Hkeys_conn_si1 & Hkeys_conn_si2)".
    {
      assert (KVS_keys = (dom m ∩ KVS_keys) ∪ (KVS_keys ∖ (dom m ∩ KVS_keys))) as Heq.
      - apply union_difference_L.
        set_solver.
      - rewrite {1} Heq.
        rewrite (big_sepS_union _ (dom m ∩ KVS_keys) (KVS_keys ∖ (dom m ∩ KVS_keys))); last set_solver.
        iDestruct "Hkeys_conn_si" as "(Hkeys_conn_si1 & Hkeys_conn_si2)".
        iSplitL "Hkeys_conn_si1".
        + iApply (big_sepS_wand with "[$Hkeys_conn_si1]").
          iApply big_sepS_intro.
          iModIntro.
          iIntros (k Hk_in) "([(%ov & %Hdom & %Himp & Hkey1)|%Hfalse] & Hkey2)"; 
            last (exfalso; set_solver).
          iExists ov; iFrame.
          iPureIntro; set_solver.
        + iApply (big_sepS_wand with "[$Hkeys_conn_si2]").
          iApply big_sepS_intro.
          iModIntro.
          iIntros (k Hk_in) "(_ & Hkey2)".
          iFrame.
          assert (k ∉ dom m) as Hdom; first set_solver.
          iPureIntro; set_solver.
    } 
    iDestruct "Hghost_map_m_conn" as "(Hghost_map_m_conn_half & Hghost_map_m_conn_half')".
    iMod ("Hclose'" with "[Hghost_map_m_conn_half Hghost_map_mnames_si Hghot_map_m_gl Hown_exec Hopen_state 
      Hopen_trans_state Htr_is' HOwnLin' Hghost_map_mname' Hghost_map_m' 
      Hghost_map_mstate' Hkeys_conn_res2 Hlin_res' Hpost_res' Hdisj_trace_res]").
    {
      iModIntro.
      iExists T', exec'.
      iSplitL "Hghost_map_mnames_si Hghot_map_m_gl Hown_exec Hopen_state Hopen_trans_state Hghost_map_m_conn_half".
      {
        iExists mnames_si; iFrame.
        iExists m_gl; iFrame.
        iSplit; first by iPureIntro.
        iSplit; first by (iPureIntro; exists st_new).
        rewrite /open_transactions_state.
        rewrite {4} Heq_sa_clients.
        rewrite big_sepS_union; last set_solver.
        iFrame.
        rewrite big_sepS_singleton.
        iRight.
        iExists c, m_conn', γm_conn, γsnap.
        iFrame.
        iSplit; first (iPureIntro; set_solver).
        iIntros (trans Hfalse).
        exfalso; set_solver.
      }
      iFrame.
      iExists t', (lt' ++ [(#tag1, (c, #"StLin"))%V]).
      iFrame.
      iSplitR.
      {
        iPureIntro.
        apply (lin_trace_lin lt' ((#tag1, (c, #"StPre"))%V) ((#tag1, (c, #"StLin"))%V) tag1 c t'); 
          try done; rewrite /is_lin_event /is_pre_event; left; by exists tag1, c.
      }
      iSplitR; first by iPureIntro.
      iSplitR.
      {
        iPureIntro.
        destruct Hex' as (Hex1 & Hex2 & Hex3).
        split.
        - intros le op Hle_in Hlin_le.
          specialize (Hex1 le op).
          apply Hex1; last done.
          rewrite elem_of_app in Hle_in.
          destruct Hle_in as [Hle_in | Hle_in]; first done.
          assert (le = (#tag1, (c, #"StLin"))%V) as ->; first set_solver.
          inversion Hlin_le.
        - split.
          + intros trans op Hin_t Hin_op.
            specialize (Hex2 trans op Hin_t Hin_op).
            set_solver.
          + intros trans op1 op2 Htrans_in Hrel.
            specialize (Hex3 trans op1 op2 Htrans_in Hrel).
            destruct Hex3 as (i & j & Hle & Hlookup_i & Hlookup_j).
            exists i, j.
            split; first done.
            split; by apply lookup_app_l_Some.
      }
      iSplitR; first by iPureIntro.
      iSplitR.
      {
        iPureIntro.
        apply valid_sequence_st_lin; set_solver.
      }
      do 2 (iSplitR; first by iPureIntro).
      iExists (<[sa:=(Active (dom m), Some c)]> mstate').
      iFrame.
      iExists mname'.
      iFrame.
      rewrite {4} Heq_sa_clients.
      rewrite big_sepS_union; last set_solver.
      iSplitL "Hkeys_conn_res2 Hghost_map_m'".
      - rewrite big_sepS_singleton.
        iRight.
        rewrite /initialized_trace_resources.
        rewrite lookup_insert.
        iExists (Active (dom m)), c, γ, m''.
        assert (c = c') as ->; first set_solver.
        iFrame "#∗".
        do 3 (iSplit; first iPureIntro; first set_solver).
        iRight.
        iExists (dom m), ((dom m) ∩ KVS_keys), [].
        do 2 (iSplit; first by iPureIntro).
        iSplitR.
        + iPureIntro.
          exists (#tag1, (c', #"StLin"))%V, lt'.
          do 2 (split; first done).
          split; first by exists tag1.
          set_solver.
        + iSplitL.
          * iApply (big_sepS_wand with "[$Hkeys_conn_res2]").
            iApply big_sepS_intro.
            iModIntro.
            iIntros (k Hk_in) "Hkey".
            iExists None.
            iFrame.
          * iIntros (k' Hk'_dom ov Hlookup).
            iPureIntro.
            destruct ov as [v|].
            -- rewrite Hnone in Hlookup; first done.
               set_solver.
            -- left.
               set_solver.
      - iApply (big_sepS_wand with "[$Hdisj_trace_res]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa' Hsa'_in) "Hsa'".
        iApply (client_trace_state_resources_neq2 sa sa' c with "[][][][$]"); try done.
        iPureIntro; set_solver.
    }
    iMod ("Hshift" with "[Hkeys_status Hkeys_conn_si1 Hkeys_conn_si2 Hghost_map_m_conn_half'
      Hkeys1 Hkeys2 Hkeys_conn Hsa_pointer Hkeys_conn_res1 Hconn_state]").
    {
      iFrame.
      iSplitL "Hkeys_conn_si2 Hsa_pointer Hghost_map_m_conn_half'".
      {
        iExists γm_conn, γsnap, m_conn'.
        iFrame "∗#".
        iRight.
        iExists m_gl, m.
        iSplit; first by iPureIntro.
        iFrame.
        iSplit; first by iPureIntro.
        iExists exec'.
        iFrame "#".
        iPureIntro.
        split; last done.
        by exists st_new.
      }
      rewrite big_sepM_sep.
      iDestruct "Hkeys2" as "(Hkeys2 & #Hkeys_hist)".
      iSplitL "Hkeys1 Hkeys2"; first (do 2 rewrite {1} big_sepM_sep; iFrame "#∗").
      iFrame "#".
      clear Hm_conn'_st_new_rel Hsubset Hm_conn'_none.
      iClear "Hseen".
      iInduction m as [|k h m Hlookup_k_m] "IH" using map_ind; first set_solver.
      rewrite dom_insert_L intersection_union_r_L.
      assert ({[k]} ∩ KVS_keys ## dom m ∩ KVS_keys) as Hdisjoint.
      {
        assert (k ∉ dom m) as Hnin; last set_solver.
        by apply not_elem_of_dom_2.
      }
      rewrite big_sepS_union; last done.
      iDestruct "Hkeys_conn_si1" as "(Hkeys_conn_si1_k & Hkeys_conn_si1)".
      rewrite big_sepS_union; last done.
      iDestruct "Hkeys_conn_res1" as "(Hkeys_conn_res1_k & Hkeys_conn_res1)".
      rewrite big_sepM_insert; last done.
      iDestruct "Hkeys_hist" as "(#Hkeys_hist_k & #Hkeys_hist)".
      rewrite big_sepM_insert; last done.
      iDestruct "Hkeys_status" as "(Hkeys_status_k & Hkeys_status)".
      rewrite big_sepM_insert; last done.
      iDestruct "Hkeys_conn" as "(Hkeys_conn_k & Hkeys_conn)".
      rewrite big_sepM_insert; last done.
      iSplitR "Hkeys_status Hkeys_conn_si1 Hkeys_conn Hkeys_conn_res1"; 
        last iApply ("IH" with "[//][$Hkeys_status][Hkeys_conn_si1][$Hkeys_conn][$Hkeys_conn_res1]");
        last first.
      {
        iApply (big_sepS_wand with "[$Hkeys_conn_si1]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (k' Hk_in) "(%ov & Hkey1 & %Hkey_pure & Hkey2)".
        iExists ov.
        iFrame.
        iPureIntro.
        intros Hk'_in.
        apply not_elem_of_dom_2 in Hlookup_k_m.
        rewrite lookup_insert_ne in Hkey_pure; set_solver.
      }
      iFrame.
      assert (c = c') as <-; first set_solver.
      destruct (decide (k ∈ KVS_keys)) as [Hk_in|Hk_nin].
      - rewrite (subseteq_intersection_1_L {[k]} KVS_keys); last set_solver.
        do 2 rewrite big_sepS_singleton.
        iDestruct "Hkeys_conn_si1_k" as "(%ov & Hkeys_conn_si1_k_1 & %Hkey_conn_si1_pure & Hkeys_conn_si1_k_2)".
        iSplitR "Hkeys_conn_si1_k_2".
        + iExists sa, γ, None.
          iFrame "#".
          iSplit; first done.
          iSplitL "Hkeys_conn_res1_k"; first (iIntros (_); iFrame).
          iSplit; first done.
          iSplit.
          {
            iIntros (v Hlast).
            apply last_Some_elem_of in Hlast.
            by iApply "Hkeys_hist_k".
          }
          iIntros (_).
          iExists γm_conn, γsnap.
          iFrame "#".
          iLeft.
          destruct Hkey_conn_si1_pure as (h' & Hlookup_m_k & Hlast_eq); first set_solver.
          rewrite lookup_insert in Hlookup_m_k.
          assert (last h = last h') as ->; first set_solver.
          rewrite Hlast_eq.
          by iFrame.
        + iExists sa, γm_conn, γsnap.
          iFrame "#".
          iSplit; first done.
          iIntros (_).
          iRight.
          iSplit; first done.
          iFrame.
      - iSplitL.
        + iExists sa, γ, None.
          iFrame "#".
          iSplit; first done.
          iSplitR; first (iIntros (Hfalse); set_solver).
          iSplit; first done.
          iSplit.
          {
            iIntros (v Hlast).
            apply last_Some_elem_of in Hlast.
            by iApply "Hkeys_hist_k".
          }
          iIntros (Hfalse); set_solver.
        + iExists sa, γm_conn, γsnap.
          iFrame "#".
          iSplit; first done.
          iIntros (Hfalse); set_solver.
    }
    iModIntro.
    rewrite /start_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%exec'' (Hinv_si_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & %Hbased'' & %Hvalid_exec'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, #"StLin"))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, #"StLin"))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; 
        rewrite /is_post_event /is_st_post_event;
        set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, #"StPost"))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, #"StPost"))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      left.
      by eexists _, _.
    }
    iMod ("Hclose''" with "[Hinv_si_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_st_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma init_client_implication γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hinit_cli".
    rewrite /init_client_proxy_spec.
    iIntros (sa Φ) "!# (Hunall & Hsock & Hmes & (Hcan & (Hsa_pointer & %Hsa_in & Hsa_pointer_si)) & Hfree) HΦ".
    rewrite /TC_init_client_proxy /KVS_wrapped_api /wrap_init_client_proxy.
    wp_pures.
    wp_bind (ast.Fresh _).
    iInv "HinvExt" as ">[%T [%exec (Hinv_si_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_in_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    rewrite /init_pre_emit_event.
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, init_pre_emit_event)%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, init_pre_emit_event)%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Hinv_si_res Htr_is HOwnLin Hlin_res Hpost_res Hstate_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, init_pre_emit_event)%V]), lt.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_in_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply ("Hinit_cli" $! sa with "[$Hunall $Hsock $Hmes $Hcan $Hfree]").
    iIntros (c) "(Hconn_state & #His_conn)".
    wp_pures.
    wp_bind (ast.Emit _).
    rewrite /init_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T' [%exec' (Hinv_si_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, #"InLin"))%V with "[$HOwnLin']") as "HOwnLin'".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, #"InPre")%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, #"InPre")%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, #"InLin"))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hstate_res'" as "[%mstate (Hghost_map_mstate & [%mname (Hghost_map_mname & Hext_rest1')])]".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mstate][$Hsa_pointer]") as "%Hlookup".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {6} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hext_rest1'" as "(Hext_rest1_sa & Hext_rest1)".
    rewrite big_sepS_singleton.
    iAssert ((⌜mname !! sa = None⌝ ∧ ⌜no_emit_with_address sa lt' extract⌝)%I) as "(%Hlookup_none & %Hno_emit)".
    {
      iDestruct ("Hext_rest1_sa") as "[(_ & %Hnot_lookup & %Hno_emit)|[%s [%c' [%γ [%m (%Hfalse & asd)]]]]]".
      - iPureIntro. 
        destruct (mname !! sa) as [γ|] eqn:Hfalse; last done.
        exfalso.
        apply Hnot_lookup.
        by exists γ.
      - set_solver.
    }
    iDestruct (res.(snapshot_isolation.specs.resources.Extraction_of_address) 
          with "[$His_conn]") as "%Hextract".
    assert (lin_trace_of (lt' ++ [(#tag1, (c, #"InLin"))%V])
      (t' ++ [(#tag1, (c, #"InPost"))%V])) as Hlin_trace'.
    {
      apply (lin_trace_valid tag1); try done.
      - right.
        split.
        + do 4 right. 
          rewrite /is_in_post_event; eauto.
        + exists (#tag1, (c, #"InLin"))%V.
          set_solver.
      - apply (lin_trace_lin lt' (#tag1, #"InPre")%V 
          (#tag1, (c, #"InLin"))%V tag1 c t'); try done;
          rewrite /is_lin_event /is_in_lin_event /is_pre_event /is_in_pre_event;
          set_solver.
    }
    assert (valid_sequence (lt' ++ [(#tag1, (c, #"InLin"))%V])) as Hvalid_seq''.
    {
      apply valid_sequence_in_lin; try done.
      eapply unique_init_events_add_init; try done.
      rewrite /valid_sequence in Hvalid_seq'; set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      exists (lt' ++ [(#tag1, (c, #"InLin"))%V]).
      split_and!; try done.
      eexists T', exec'.
      split_and!; try done.
      apply extraction_of_add_init_lin; rewrite /is_in_lin_event;
        set_solver.
    }
    iIntros "Htr_is".
    iDestruct (lin_tag_add_post (lt' ++ [(#tag1, (c, #"InLin"))%V]) t' γmlin (#tag1, (c, #"InPost"))%V 
      with "[$Hlin_res']") as "Hlin_res'".
    iDestruct (post_tag_add t' γmpost (#tag1, (c, #"InPost"))%V tag1 with "[$Hpost_res' $Hpost_tag_res]")
      as "Hpost_res'".
    {
      iPureIntro.
      simpl.
      split; first done.
      do 4 right.
      rewrite /is_in_post_event.
      by eexists _, _.
    }
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γ (Hghost_map_m & Hghost_elems_m)]".
    iMod (ghost_map_update (CanStart, Some c) with "[$Hghost_map_mstate] [$Hsa_pointer]") 
      as "(Hghost_map_mstate & Hsa_pointer)".
    iMod (ghost_map_insert_persist sa (γ, c) Hlookup_none with "[$Hghost_map_mname]") 
      as "(Hghost_map_mname & #Hkey_pers_mname)".
    iDestruct "Hinv_si_res'" as "(%mname_si & Hghost_map_mname_si & %m_si & Hghost_map_m_si & 
      %Hkeys_some_m_si & Hown_exec & %Hrel_exe_map & Hopen_si)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mname_si][$Hsa_pointer_si]") as "%Hlookup_none'".
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γm_conn ((Hghost_map_m_si'_half & Hghost_map_m_si'_half') & Hghost_elems_m_si')]".
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γsnap (Hghost_map_m_si'' & Hghost_elems_m_si'')]".
    iMod (ghost_map_update (Some (γm_conn, γsnap, c)) with "[$Hghost_map_mname_si] [$Hsa_pointer_si]") 
      as "(Hghost_map_mname_si & Hsa_pointer_si)".
    iMod (ghost_map_elem_persist (K:=socket_address) (V:=option (gname * gname * val)) 
      with "[$Hsa_pointer_si]") as "#Hsa_pointer_si".
    assert (¬∃ t, open_trans t c T') as Hnot_open.
    {
      intros (trans & (op & Hin & Hlast & Hconn & _)).
      apply Hno_emit.
      destruct Hex' as (_ & Hex' & _).
      exists (toLinEvent op), c.
      split_and!; try done.
      - apply last_Some_elem_of in Hlast; set_solver.
      - by apply conn_event_op.
    }
    iMod ("Hclose'" with "[Hghost_map_m_si'_half Hghost_map_m_si Hown_exec Hopen_si Hghost_map_mname_si
      Htr_is HOwnLin' Hghost_map_mname Hext_rest1 Hext_rest1_sa 
      Hghost_map_mstate Hghost_map_m Hghost_elems_m Hlin_res' Hpost_res']").
    {
      iNext.
      iExists T', exec'.
      iSplitL "Hghost_map_m_si'_half Hghost_map_m_si Hown_exec Hopen_si Hghost_map_mname_si".
      {
        iExists (<[sa:=Some (γm_conn, γsnap, c)]> mname_si); iFrame.
        iExists m_si; iFrame.
        do 2 (iSplit; first by iPureIntro).
        rewrite /open_transactions_state.
        rewrite {3} Heq_sa_clients.
        rewrite {4} Heq_sa_clients.
        do 2 (rewrite big_sepS_union; last set_solver).
        iDestruct "Hopen_si" as "(_ & Hopen_si)".
        iSplitL "Hghost_map_m_si'_half".
        - iApply big_sepS_singleton.
          rewrite lookup_insert.
          iRight.
          iExists c, (gset_to_gmap None KVS_keys), γm_conn, γsnap.
          iSplit; first (iPureIntro; set_solver).
          iFrame.
          iIntros (trans Hfalse).
          iPureIntro; set_solver.
        - iApply (big_sepS_wand with "[$Hopen_si]").
          iApply big_sepS_intro.
          iModIntro.
          iIntros (sa' Hsa'_in) "Hres".
          rewrite lookup_insert_ne; last set_solver.
          iFrame.
      }
      iExists (t' ++ [(#tag1, (c, #"InPost"))%V]), (lt' ++ [(#tag1, (c, #"InLin"))%V]).
      iFrame.
      do 2 (iSplit; first by iPureIntro).
      iSplit; first iPureIntro.
      {
        apply extraction_of_add_init_lin; rewrite /is_in_lin_event;
        set_solver.
      }
      do 4 (iSplit; first by iPureIntro).
      iClear "HinvExt Hinit_cli Htr_inv".
      iExists (<[sa:=(CanStart, Some c)]> mstate).
      iFrame.
      iExists (<[sa:=(γ, c)]> mname).
      iFrame.
      rewrite {2} Heq_sa_clients.
      rewrite big_sepS_union; last set_solver.
      iSplitL "Hghost_map_m Hghost_elems_m".
      + iApply big_sepS_singleton.
        iRight.
        iExists CanStart, c, γ, (gset_to_gmap None KVS_keys).
        rewrite lookup_insert.
        iFrame "#∗".
        do 2 (iSplit; first by iPureIntro).
        iSplit.
        {
          iPureIntro.
          exists (#tag1, (c, #"InLin"))%V.
          simpl.
          rewrite /is_in_lin_event.
          split_and!; try done; eauto.
          apply elem_of_app.
          right.
          set_solver.
        }
        iLeft.
        iSplit; first by iPureIntro.
        iSplit.
        * iPureIntro.
          rewrite /commit_closed.
          intros e_st Hin Hconn Hstart.
          exfalso.
          apply Hno_emit.
          assert (e_st ∈ lt') as Hin_st; last set_solver.
          rewrite elem_of_app in Hin.
          destruct Hin as [Hin|Hin]; first done.
          rewrite /is_st_lin_event in Hstart.
          set_solver.
        * iSplit. 
          -- iPureIntro.
             intros (trans & (op & Ht'_in & Hlast & Hconn_last & _)).
             destruct Hex' as (_ & Hex' & _).
             apply last_Some_elem_of in Hlast.
             specialize (Hex' trans op Ht'_in Hlast).
             apply Hno_emit.
             exists (toLinEvent op), c.
             split_and!; try done.
             destruct op; destruct s; 
              simpl in Hconn_last; subst; 
              simpl; try done.
              by destruct ov.
          -- rewrite big_sepM_gset_to_gmap.
             iApply (big_sepS_wand with "[$Hghost_elems_m]").
             iApply big_sepS_intro.
             iModIntro.
             iIntros (k Hk_in) "Hkey".
             iExists None.
             iFrame.
      + iApply (big_sepS_wand with "[$Hext_rest1]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa' Hsa'_in) "Hext_res".
        iApply (client_trace_state_resources_neq3 sa sa' c with "[][][][$]"); try done.
        iPureIntro; set_solver.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    rewrite /ConnectionState.
    simpl.
    iFrame "∗#".
    iSplitL.
    - iExists γm_conn, γsnap, (gset_to_gmap None KVS_keys).
      iFrame "∗#".
      iLeft.
      iSplit; first by iPureIntro.
      iFrame.
      do 2 (rewrite big_sepM_gset_to_gmap).
      iAssert (([∗ set] k ∈ KVS_keys, ghost_map_elem γm_conn k (DfracOwn 1%Qp) None) ∗ 
        ([∗ set] k ∈ KVS_keys, ghost_map_elem γsnap k (DfracOwn 1%Qp) None))%I with 
        "[Hghost_elems_m_si' Hghost_elems_m_si'']" as "Hghost_maps"; first iFrame.
      rewrite -(big_sepS_sep).
      iApply (big_sepS_wand with "[$Hghost_maps]").
      iApply big_sepS_intro.
      iModIntro.
      iIntros (k Hk_in) "(Hptr1 & Hptr2)".
      iExists None; iFrame.
    - do 2 (iSplit; first by iPureIntro).
      iExists γ.
      iFrame "#".
      iExists γm_conn, γsnap.
      iFrame "#".
  Qed.

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((SI_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_si ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    SI_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & #Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv & %Hkvs_inv_name)".
    iMod (ghost_map_alloc ((gset_to_gmap (CanStart, None) clients : 
      gmap socket_address (local_state * option val))))
      as "[%γmstate (Hghost_map_mstate & Hghost_elems_mstate)]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmlin Hghost_map_mlin]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmpost Hghost_map_mpost]".
    iMod (ghost_map_alloc_empty (K:=socket_address) (V:=(gname * val))) as "[%γmname Hghost_map_mname]".
    iMod (own_alloc (●ML ([] : list val) ⋅ ◯ML ([] : list val))) as (γl) "[Hltrace _]".
    { 
      apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. 
    }
    iMod (ghost_map_alloc ((gset_to_gmap [] KVS_keys : gmap Key (list val))))
      as "[%γm_gl (Hghost_map_mmap & Hghost_elems_mmap)]".
    iMod (own_alloc (A:=mono_listUR (leibnizO (transaction * state)))
      (●ML [] ⋅ ◯ML [])) as (γexec) "[Hexec_trace _]".
    { 
      apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. 
    }
    iMod (own_log_auth_update _ _ ([] ++ [([], ∅)]) with "[$Hexec_trace]") as "Hexec_trace"; 
      first by apply prefix_app_r.
    iMod (ghost_map_alloc ((gset_to_gmap None clients : gmap socket_address (option (gname * gname * val)))))
      as "[%γsi_name (Hghost_map_msi_name & Hghost_elems_msi_name)]".
    iMod (inv_alloc KVS_InvName ⊤ (∃ T exec, GlobalInvExtSI γm_gl γexec γsi_name T exec extract clients ∗ 
      GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) with 
      "[Htr Hghost_map_mstate Hghost_map_mlin Hghost_map_mpost Hghost_map_mname Hltrace 
      Hghost_map_mmap Hghost_map_msi_name Hexec_trace]") as "#HinvExt".
    {
      iNext.
      iExists [], [([], ∅)].
      iSplitL "Hghost_map_mmap Hghost_map_msi_name Hexec_trace".
      {
        iExists (gset_to_gmap None clients).
        iFrame.
        iExists (gset_to_gmap [] KVS_keys).
        iFrame.
        iSplit.
        - iPureIntro.
          intros k Hk_in.
          assert (gset_to_gmap [] KVS_keys !! k = Some []) as ->; last done.
          by apply lookup_gset_to_gmap_Some.
        - iSplit; first (iPureIntro; apply rel_exec_map_init).
          rewrite /open_transactions_state.
          iApply big_sepS_intro.
          iModIntro.
          iIntros (sa Hsa_in).
          iLeft.
          iPureIntro.
          by apply lookup_gset_to_gmap_Some.
      }
      iExists [], [].
      iFrame.
      simpl.
      iSplitR.
      {
        iPureIntro.
        rewrite /lin_trace_of /rel_list.
        set_solver.
      }
      iSplitR; first iPureIntro; first set_solver.
      iSplitR.
      {
        iPureIntro.
        rewrite /extraction_of.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_transactions.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_sequence /unique_init_events.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /based_on.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /commit_test_si /valid_execution /complete /no_conf.
        split_and!; try done.
        - intros i e1 e2 _ Hfalse.
          rewrite list_lookup_singleton_Some in Hfalse.
          lia.
        - intros t Ht_in.
          assert (t = []) as ->; first set_solver.
          exists ∅, 0.
          set_solver.
        - simpl.
          intros t1 t2 i j Hlookup_i Hlookup_j Heq.
          rewrite list_lookup_singleton_Some in Hlookup_i.
          rewrite list_lookup_singleton_Some in Hlookup_j.
          lia.
      }
      iClear "Hinit_kvs Hinit_cli Hread Hstart Hwrite Hcom".
      iSplitR "Hghost_map_mlin Hghost_map_mpost".
      - iExists (gset_to_gmap (CanStart, None) clients).
        iFrame.
        iExists ∅.
        iFrame.
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa Hin).
        iLeft.
        iSplit.
        + iRight.
          iPureIntro.
          by rewrite lookup_gset_to_gmap_Some.
        + iSplit.
          * iPureIntro.
            set_solver.
          * iPureIntro.
            rewrite /no_emit_with_address.
            set_solver.
      - iSplitL "Hghost_map_mlin". 
        + iExists ∅.
          iFrame.
          iSplitL; first set_solver.
          iIntros (tag Hexists). 
          set_solver.
        + iExists ∅.
          iFrame.
          iSplitL; first set_solver.
          iIntros (tag Hexists).
          set_solver.
    }
    iModIntro.
    iExists (wrapped_resources γmstate γmlin γmpost γmname γl γm_gl γexec γsi_name clients res).
    iFrame "Hkvs_init".
    iSplitL "Hkeys Hghost_elems_mmap".
    {
      simpl.
      rewrite big_sepM_gset_to_gmap.
      rewrite big_sepS_sep.
      iFrame.
      iApply (big_sepS_mono with "[$Hghost_elems_mmap]").
      iIntros (k Hin) "Hkey". 
      iFrame.
      iIntros (v Hfalse).
      exfalso.
      set_solver.
    }
    iSplitR; iFrame "∗#".
    iSplitL "Hghost_elems_mstate Hcan_conn Hghost_elems_msi_name".
    { 
      simpl.
      do 2 rewrite big_sepM_gset_to_gmap.
      do 2 rewrite big_sepS_sep.
      iFrame.
      iApply (big_sepS_mono with "[$Hghost_elems_msi_name]").
      iIntros (sa Hin) "Hkey".
      by iFrame.
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hstart Hwrite Hread Hcom".
      iApply (init_client_implication with "[//][$Htr_inv][$HinvExt][$Hinit_cli]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hwrite Hstart Hcom".
      iApply (read_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E k) "!# #Hsub #Hin #Hconn %Φ !# Hshift".
      iApply ("Hread" $! c sa E k with "[$][$][$][$Hshift]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hread Hstart Hcom".
      iApply (write_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E k v) "!# #Hsub #Hin #Hconn %Φ !# Hshift".
      iApply ("Hwrite" $! c sa E k v with "[$][$][$][$Hshift]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hwrite Hread Hcom".
      iApply (start_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E) "!# #Hsub #Hconn %Φ !# Hshift".
      iApply ("Hstart" $! c sa E with "[$][$][$Hshift]").
    }
    iClear "Hinit_kvs Hinit_cli Hwrite Hread Hstart".
    iApply (commit_implication with "[//][$Htr_inv][$HinvExt][]").
    iIntros (c sa E) "!# #Hsub #Hconn %Φ !# Hshift".
    iApply ("Hcom" $! c sa E with "[$][$][$Hshift]").
  Qed.

End trace_proof.
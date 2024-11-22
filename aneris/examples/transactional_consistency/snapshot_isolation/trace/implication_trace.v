From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
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
      (∀ k ov h, s !! k = ov ↔ (m !! k = Some h ∧ last h = ov)) ∧
      (∀ k h, m !! k = Some h → ind_rel_exec_map k exec h).

  Definition reads_from_last_state (exec : execution) (k : Key) (ov : option val) := 
    ∃ s, last (split exec).2 = Some s ∧ s !! k = ov.

  Definition OwnExecHist (γ : gname) (exec : execution) : iProp Σ :=
    True.

  Definition OwnExec (γ : gname) (exec : execution) : iProp Σ := 
    True.

  Definition local_key_state (γsi_name : gname) (sa : socket_address) (c : val) (k : Key) (ov ov' : option val) : iProp Σ := 
    ∃ (γ' γ'' γ''' : gname), ghost_map_elem γsi_name sa DfracDiscarded (γ', γ'', γ''', c) ∗
      ((⌜ov' = None⌝ ∗ ghost_map_elem γ' k (DfracOwn 1%Qp) ov) ∨ 
      (∃ v, ⌜ov' = Some v ∧ ov = ov'⌝ ∗ ghost_map_elem γ'' k (DfracOwn 1%Qp) None)).

  Definition inactive_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) 
  (γmstate γ' γ'' γ''' : gname) : iProp Σ := 
    ⌜s = aux_defs.CanStart⌝ ∗ ∃ st,  own γ''' (to_dfrac_agree (DfracOwn 1) st) ∗
    ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, Some c) ∗
    ([∗ set] k ∈ KVS_keys, ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗
      ghost_map_elem γ'' k (DfracOwn 1%Qp) None).

  Definition active_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) (γexec γmstate γ' γ'' γ''' : gname) 
  (m : gmap Key (option val)) : iProp Σ := 
    ∃ (ms : gmap Key (list val)), ⌜s = aux_defs.Active ms⌝ ∗ ⌜∀ k ov, m !! k = Some ov ↔ (∃ h, ms !! k = Some h ∧ last h = ov)⌝ ∗ 
      ∃ exec_pre, OwnExecHist γexec exec_pre ∗ ⌜rel_exec_map exec_pre ms⌝ ∗
        ∃ st, own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st) ∗ ⌜∀ k ov, st !! k = ov ↔ (∃ h, ms !! k = Some h ∧ last h = ov)⌝ ∗
          ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.Active (dom ms), Some c) ∗
          ([∗ set] k ∈ KVS_keys ∖ (dom ms), ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗
            ghost_map_elem γ'' k (DfracOwn 1%Qp) None).

  Definition connection_exec_state (s : aux_defs.local_state) (sa : socket_address) (c : val) (γexec γmstate γ' γ'' γ''' : gname) 
  (m : gmap Key (option val)) : iProp Σ := 
    inactive_connection_exec_state s c sa γmstate γ' γ'' γ''' ∨ active_connection_exec_state s c sa γexec γmstate γ' γ'' γ''' m.

  Definition open_transactions_state (T : list transaction) (mnames : gmap socket_address (gname * gname * gname * val)) 
  (extract : val → option val) : iProp Σ := 
    ([∗ list] _↦(trans : transaction) ∈ T, ∃ (op : operation), ⌜last trans = Some op⌝ ∧ (⌜is_cm_op op⌝ ∨ 
      (∃ (c : val) (st : gmap Key val) (sa : socket_address) (γ γ'' γ''' : gname), 
        ⌜open_trans trans c T⌝ ∗ ⌜extract c = Some #sa ∧ mnames !! sa = Some (γ, γ'', γ''', c)⌝ ∗
        own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st) ∗
        ⌜∀ sig k v, (Rd sig k (Some v)) ∈ trans → 
        ¬ (∃ sig' v', rel_list trans (Wr sig' k v') (Rd sig k (Some v))) →  st !! k = Some v⌝))).

  Definition GlobalInvExtSI (γmap γexec γsi_mstate γsi_name : gname) (T : list transaction) (exec : execution)
  (extract : val → option val) (clients : gset socket_address) : iProp Σ := 
    ∃ (mstate : gmap socket_address (option val)), ghost_map_auth γsi_mstate (1%Qp) mstate ∗ 
    ∃ (mnames : gmap socket_address (gname * gname * gname * val)), ghost_map_auth γsi_name (1%Qp) mnames ∗
      ⌜∀ sa, ((mstate !! sa = None ∧ mnames !! sa = None) ∨ (∃ (c : val), mstate !! sa = Some (Some c)))⌝ ∗
    ∃ (m : gmap Key (list val)), 
      ghost_map_auth γmap (1%Qp) m ∗ OwnExec γexec exec ∗ ⌜rel_exec_map exec m⌝ ∗ 
      open_transactions_state T mnames extract.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources (γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name : gname) (clients : gset socket_address)
  `(res : !SI_resources Mdl Σ) : SI_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_rc ∗ 
                    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                    GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec))%I;
      OwnMemKey k h := (OwnMemKey k h ∗ ghost_map_elem γmap k (DfracOwn 1%Qp) h ∗
                        (∀ v, ⌜v ∈ h⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                          ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗  ∃ (sa : socket_address) γ ov', ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                             ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov') ∗ ⌜sa ∈ clients⌝ ∗ 
                             ⌜∀ v, ov' = Some v → k ∈ KVS_keys⌝ ∗
                             (∀ v, ⌜ov' = Some v⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝) ∗
                             local_key_state γsi_name sa c k ov ov')%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γsi_mstate sa (DfracOwn 1%Qp) (Some c) ∗
                                 ∃ (γ' γ'' γ''' : gname) (m : gmap Key (option val)), ghost_map_elem γsi_name sa DfracDiscarded (γ', γ'', γ''', c) ∗
                                   ghost_map_auth γ' (1%Qp) m ∗ connection_exec_state s sa c γexec γmstate γ' γ'' γ''' m)%I;
      IsConnected c sa := (IsConnected c sa ∗ ⌜sa ∈ clients⌝ ∗ ⌜extract c = Some #sa⌝ ∗ 
                           ∃ (γ : gname), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                           ∃ (γ' γ'' γ''' : gname), ghost_map_elem γsi_name sa DfracDiscarded (γ', γ'', γ''', c))%I;
      KVS_si := KVS_si;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ 
                                  ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, None) ∗ ⌜sa ∈ clients⌝ ∗
                                  ghost_map_elem γsi_mstate sa (DfracOwn 1%Qp) None)%I;
      KeyUpdStatus c k b := (KeyUpdStatus c k b ∗ ∃ (sa : socket_address) (γ' γ'' γ''' : gname), ⌜extract c = Some #sa⌝ ∗
                              ghost_map_elem γsi_name sa DfracDiscarded (γ', γ'', γ''', c) ∗ 
                              ((⌜b = true⌝ ∧ ∃ ov, ghost_map_elem γ' k (DfracOwn 1%Qp) ov) ∨ 
                               (⌜b = false⌝ ∧ ghost_map_elem γ'' k (DfracOwn 1%Qp) None)))%I;
      Seen k V := Seen k V%I;
      extract c := res.(snapshot_isolation.specs.resources.extract) c;
    |}.
  Next Obligation.
    iIntros (??????????????) "(Hkey & [%sa [%γ [%ov' (Hghost_elem_per & %Hextract & Hghost_elem  & %Hin_sa & Hlin_hist & Hstate)]]])".
    iDestruct (res.(snapshot_isolation.specs.resources.OwnLocalKey_serializable) 
      with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iExists sa, γ, ov'.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (??????????????).
    iIntros (??) "#(HGinv & Hinv) (#Hseen & Hkey & Hin)".
    iMod (res.(snapshot_isolation.specs.resources.Seen_valid) 
      with "[$HGinv][$Hseen $Hkey]") as "(Hkey & Hsub)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (???????????????) "#(HGinv & Hinv) (Hkey & Hin)".
    iMod (res.(snapshot_isolation.specs.resources.Seen_creation) 
      with "[$HGinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????? clients res sa c) "(Hconn & _)".
    iApply (res.(snapshot_isolation.specs.resources.Extraction_of_address) 
      with "[$Hconn]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????????).
    iIntros (clients res sa sa' c c' Heq1 Heq2 Hneq).
    by eapply res.(snapshot_isolation.specs.resources.Extraction_preservation).
  Qed.

  (** Helper lemmas *)

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
      by rewrite -app_nil_end_deprecated in Hrel.
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

  (** Per operation implications *)

  Lemma init_client_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients res).
  Proof.
  Admitted.

  Lemma start_implicationγtrans γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients res).
  Proof.
  Admitted.

  Lemma write_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients res).
  Proof.
  Admitted.

  Lemma read_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients res).
  Proof.
  Admitted.

  Lemma commit_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_mstate γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_mstate γsi_name clients res).
  Proof.
  Admitted.

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((SI_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_si ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    SI_spec clients (KVS_wrapped_api lib).
  Proof.
  Admitted.

End trace_proof.
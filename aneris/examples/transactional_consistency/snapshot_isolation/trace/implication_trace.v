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

  Definition local_key_state (γsi_name : gname) (sa : socket_address) (c : val) (k : Key) (ov ov' : option val) : iProp Σ := 
    ∃ (γ' γ'' γ''' : gname), ghost_map_elem γsi_name sa DfracDiscarded (Some (γ', γ'', γ''', c)) ∗
      ((⌜ov' = None⌝ ∗ ghost_map_elem γ' k (DfracOwn 1%Qp) ov) ∨ 
      (∃ v, ⌜ov' = Some v ∧ ov = ov'⌝ ∗ ghost_map_elem γ'' k (DfracOwn 1%Qp) None)).

  Definition inactive_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) 
  (γmstate γ' γ'' γ''' : gname) : iProp Σ := 
    ⌜s = aux_defs.CanStart⌝ ∗ ∃ (st : gmap Key val), own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st) ∗
    ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, Some c) ∗
    ([∗ set] k ∈ KVS_keys, ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗
      ghost_map_elem γ'' k (DfracOwn 1%Qp) None).

  Definition active_connection_exec_state (s : aux_defs.local_state) (c : val) (sa : socket_address) (γexec γmstate γ' γ'' γ''' : gname) 
  (m : gmap Key (option val)) : iProp Σ := 
    ∃ (ms : gmap Key (list val)), ⌜s = aux_defs.Active ms⌝ ∗ ⌜∀ k ov, m !! k = Some ov ↔ (∃ h, ms !! k = Some h ∧ last h = ov)⌝ ∗ 
      ∃ exec_pre m_pre, OwnExecHist γexec exec_pre ∗ ⌜rel_exec_map exec_pre ms ∧ ms ⊆ m_pre⌝ ∗
        ∃ st, own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st) ∗ ⌜∀ k ov, st !! k = ov ↔ (∃ h, ms !! k = Some h ∧ last h = ov)⌝ ∗
          ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.Active (dom ms), Some c) ∗
          ([∗ set] k ∈ KVS_keys ∖ (dom ms ∩ KVS_keys), ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗
            ghost_map_elem γ'' k (DfracOwn 1%Qp) None).

  Definition connection_exec_state (s : aux_defs.local_state) (sa : socket_address) (c : val) (γexec γmstate γ' γ'' γ''' : gname) 
  (m : gmap Key (option val)) : iProp Σ := 
    inactive_connection_exec_state s c sa γmstate γ' γ'' γ''' ∨ active_connection_exec_state s c sa γexec γmstate γ' γ'' γ''' m.

  Definition open_transactions_state (T : list transaction) (mnames : gmap socket_address (option (gname * gname * gname * val))) 
  (extract : val → option val) (clients : gset socket_address): iProp Σ := 
     ([∗ set] (sa : socket_address) ∈ clients, (⌜mnames !! sa = Some None⌝) ∨
      (∃ c st (γ γ'' γ''' : gname), ⌜extract c = Some #sa ∧ mnames !! sa = Some (Some (γ, γ'', γ''', c))⌝ ∗
       own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st) ∗
       ∀ trans, ⌜(open_trans trans c T) → ∀ sig k v, (Rd sig k (Some v)) ∈ trans → 
        ¬ (∃ sig' v', rel_list trans (Wr sig' k v') (Rd sig k (Some v))) →  st !! k = Some v⌝)).

  Definition GlobalInvExtSI (γmap γexec γsi_name : gname) (T : list transaction) (exec : execution)
  (extract : val → option val) (clients : gset socket_address) : iProp Σ := 
    ∃ (mnames : gmap socket_address (option (gname * gname * gname * val))), ghost_map_auth γsi_name (1%Qp) mnames ∗ 
    ∃ (m : gmap Key (list val)), ghost_map_auth γmap (1%Qp) m ∗ OwnExec γexec exec ∗ ⌜rel_exec_map exec m⌝ ∗ 
    open_transactions_state T mnames extract clients.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources (γmstate γmlin γmpost γmname γl γmap γexec γsi_name : gname) (clients : gset socket_address)
  `(res : !SI_resources Mdl Σ) : SI_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_si ∗ 
                    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                    GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec))%I;
      OwnMemKey k h := (OwnMemKey k h ∗ ghost_map_elem γmap k (DfracOwn 1%Qp) h ∗
                        (∀ v, ⌜v ∈ h⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                          ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗  ∃ (sa : socket_address) γ ov', ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                             ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov') ∗ ⌜sa ∈ clients⌝ ∗ 
                             ⌜∀ v, ov' = Some v → k ∈ KVS_keys⌝ ∗
                             (∀ v, ⌜ov' = Some v⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝) ∗
                             local_key_state γsi_name sa c k ov ov')%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ 
                                 ∃ (γ' γ'' γ''' : gname) (m : gmap Key (option val)), ghost_map_elem γsi_name sa DfracDiscarded (Some (γ', γ'', γ''', c)) ∗
                                   ghost_map_auth γ' (1%Qp) m ∗ connection_exec_state s sa c γexec γmstate γ' γ'' γ''' m)%I;
      IsConnected c sa := (IsConnected c sa ∗ ⌜sa ∈ clients⌝ ∗ ⌜extract c = Some #sa⌝ ∗ 
                           ∃ (γ : gname), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                           ∃ (γ' γ'' γ''' : gname), ghost_map_elem γsi_name sa DfracDiscarded (Some (γ', γ'', γ''', c)))%I;
      KVS_si := KVS_si;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ 
                                  ghost_map_elem γmstate sa (DfracOwn 1%Qp) (transactional_consistency.aux_defs.CanStart, None) ∗ ⌜sa ∈ clients⌝ ∗
                                  ghost_map_elem γsi_name sa (DfracOwn 1%Qp) (None : option (gname * gname * gname * val)))%I;
      KeyUpdStatus c k b := (KeyUpdStatus c k b ∗ ∃ (sa : socket_address) (γ' γ'' γ''' : gname), ⌜extract c = Some #sa⌝ ∗
                              ghost_map_elem γsi_name sa DfracDiscarded (Some (γ', γ'', γ''', c)) ∗ 
                              ((⌜b = true⌝ ∧ ∃ ov, ghost_map_elem γ' k (DfracOwn 1%Qp) ov) ∨ 
                               (⌜b = false⌝ ∧ ghost_map_elem γ'' k (DfracOwn 1%Qp) None)))%I;
      Seen k V := Seen k V%I;
      extract c := res.(snapshot_isolation.specs.resources.extract) c;
    |}.
  Next Obligation.
    iIntros (?????????????) "(Hkey & [%sa [%γ [%ov' (Hghost_elem_per & %Hextract & Hghost_elem  & %Hin_sa & Hlin_hist & Hstate)]]])".
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

  (** Per operation implications *)

  Lemma start_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
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
    iMod "Hshift" as "[%m (((Hconn_state & %γ' & %γ'' & %γ''' & %m_conn & #Hsa_pointer_si & Hghost_map_m_conn &
      Hconn_exec_state) & Hkeys) & Hshift)]".
    iDestruct "Hconn_exec_state" as "[(_ & %st & Hfrag_half & Hsa_pointer & Hkeys_conn_si)|(%ms_si & %Hfalse & _)]"; 
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
    iDestruct "Hinv_si_res'" as "(%mnames_si & Hghost_map_mnames_si & %m_si & Hghot_map_m_si & 
      Hown_exec & %Hrel_exec & Hopen_trans_state)".
    iDestruct (get_obs with "Hown_exec") as "#Hown_exec_hist".
    rewrite /open_transactions_state.
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hopen_trans_state" as "(Hopen_trans_state_sa & Hopen_trans_state)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mnames_si][$Hsa_pointer_si]") as "%Hlookup'".
    iDestruct "Hopen_trans_state_sa" as "[%Hfalse|(%c_sa & %st_sa & %γ_sa & %γ''_sa & %γ'''_sa & %Hextract_c_sa 
      & Hfrag_half' & Hopen_state)]"; first (exfalso; set_solver).
    assert (∃ (st_new : gmap Key val), ∀ k ov, st_new !! k = ov ↔ (∃ h, m_si !! k = Some h ∧ last h = ov)) 
      as (st_new & Hst_new_rel).
    {
      admit.
    }
    iAssert (|==> (own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st_new) ∗ 
      own γ''' (to_dfrac_agree (DfracOwn (1 / 2)) st_new)))%I 
      with "[Hfrag_half Hfrag_half']" as ">(Hfrag_half & Hfrag_half')".
    {
      assert (γ''' = γ'''_sa) as <-; first set_solver.
      rewrite -own_op. 
      iApply (own_update_2 with "[$Hfrag_half][$Hfrag_half']").
      apply dfrac_agree_update_2.
      rewrite dfrac_op_own. 
      by rewrite Qp.half_half.
    }
    iAssert ((|==> (([∗ set] k ∈ KVS_keys, ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗ 
      ghost_map_elem γ'' k (DfracOwn 1%Qp) None) ∗ 
      (∃ m_conn', ghost_map_auth γ' 1 m_conn' ∧ ⌜∀ k ov, k ∈ KVS_keys → (m_conn' !! k = Some ov ↔ st_new !! k = ov)⌝)))%I)
      with "[Hghost_map_m_conn Hkeys_conn_si]" as ">(Hkeys_conn_si & (%m_conn' & Hghost_map_m_conn & %Hm_conn'_st_new_rel))".
    {
      admit.
    }
    iAssert ((([∗ set] k ∈ (dom m) ∩ KVS_keys, ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗ 
      ghost_map_elem γ'' k (DfracOwn 1%Qp) None) ∗ 
      ([∗ set] k ∈ KVS_keys ∖ ((dom m) ∩ KVS_keys), ∃ (ov : option val), ghost_map_elem γ' k (DfracOwn 1%Qp) ov ∗ 
      ghost_map_elem γ'' k (DfracOwn 1%Qp) None))%I) 
      with "[Hkeys_conn_si]" as "(Hkeys_conn_si1 & Hkeys_conn_si2)".
    {
      assert (KVS_keys = (dom m ∩ KVS_keys) ∪ (KVS_keys ∖ (dom m ∩ KVS_keys))) as Heq.
      - apply union_difference_L.
        set_solver.
      - rewrite {1} Heq.
        rewrite (big_sepS_union _ (dom m ∩ KVS_keys) (KVS_keys ∖ (dom m ∩ KVS_keys))); last set_solver.
        iFrame.
    }
    iMod ("Hclose'" with "[Hfrag_half Hghost_map_mnames_si Hghot_map_m_si Hown_exec Hopen_state 
      Hopen_trans_state Htr_is' HOwnLin' Hghost_map_mname' Hghost_map_m' 
      Hghost_map_mstate' Hkeys_conn_res2 Hlin_res' Hpost_res' Hdisj_trace_res]").
    {
      iModIntro.
      iExists T', exec'.
      iSplitL "Hghost_map_mnames_si Hghot_map_m_si Hown_exec Hopen_state Hopen_trans_state Hfrag_half".
      {
        iExists mnames_si; iFrame.
        iExists m_si; iFrame.
        iSplit; first by iPureIntro.
        rewrite /open_transactions_state.
        rewrite {4} Heq_sa_clients.
        rewrite big_sepS_union; last set_solver.
        iFrame.
        rewrite big_sepS_singleton.
        iRight.
        iExists c, st_new, γ', γ'', γ'''.
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
    iMod ("Hshift" with "[Hkeys_conn_si1 Hkeys_conn_si2 Hghost_map_m_conn Hfrag_half' 
      Hkeys1 Hkeys2 Hkeys_conn Hsa_pointer Hkeys_conn_res1 Hconn_state]").
    {
      iFrame.
      iSplitL "Hkeys_conn_si2 Hsa_pointer Hghost_map_m_conn Hfrag_half'".
      {
        iExists γ', γ'', γ''', m_conn'.
        iFrame "∗#".
        iRight.
        iExists m; iSplit; first by iPureIntro.
        iFrame.
        iSplit.
        - iPureIntro.
          admit.
        - iExists exec', m_si.
          iFrame "#".
          iSplit.
          + iPureIntro.
            admit.
          + iExists st_new.
            iFrame.
            iPureIntro.
            admit.
      }
      iSplitL "Hkeys1 Hkeys2"; first (do 3 rewrite {1} big_sepM_sep; iFrame).
      iFrame "#".
      admit.
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
  Admitted.

  Lemma init_client_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
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
      Hown_exec & %Hrel_exe_map & Hopen_si)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mname_si][$Hsa_pointer_si]") as "%Hlookup_none'".
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γ' (Hghost_map_m_si' & Hghost_elems_m_si')]".
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γ'' (Hghost_map_m_si'' & Hghost_elems_m_si'')]".
    iMod (own_alloc (to_dfrac_agree (DfracOwn (1 / 2)) (∅ : gmap Key val) ⋅
      to_dfrac_agree (DfracOwn (1 / 2)) (∅ : gmap Key val))) as (γ''') "(Hfrac_res1 & Hfrac_res2)"; 
      first by rewrite -frac_agree_op.
    iMod (ghost_map_update (Some (γ', γ'', γ''', c)) with "[$Hghost_map_mname_si] [$Hsa_pointer_si]") 
      as "(Hghost_map_mname_si & Hsa_pointer_si)".
    iMod (ghost_map_elem_persist (K:=socket_address) (V:=option (gname * gname * gname * val)) 
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
    iMod ("Hclose'" with "[Hfrac_res1 Hghost_map_m_si Hown_exec Hopen_si Hghost_map_mname_si
      Htr_is HOwnLin' Hghost_map_mname Hext_rest1 Hext_rest1_sa 
      Hghost_map_mstate Hghost_map_m Hghost_elems_m Hlin_res' Hpost_res']").
    {
      iNext.
      iExists T', exec'.
      iSplitL "Hfrac_res1 Hghost_map_m_si Hown_exec Hopen_si Hghost_map_mname_si".
      {
        iExists (<[sa:=Some (γ', γ'', γ''', c)]> mname_si); iFrame.
        iExists m_si; iFrame.
        iSplit; first by iPureIntro.
        rewrite /open_transactions_state.
        rewrite {3} Heq_sa_clients.
        rewrite {4} Heq_sa_clients.
        do 2 (rewrite big_sepS_union; last set_solver).
        iDestruct "Hopen_si" as "(_ & Hopen_si)".
        iSplitL "Hfrac_res1".
        - iApply big_sepS_singleton.
          rewrite lookup_insert.
          iRight.
          iExists c, ∅, γ', γ'', γ'''.
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
    - iExists γ', γ'', γ''', (gset_to_gmap None KVS_keys).
      iFrame "∗#".
      iLeft.
      iSplit; first by iPureIntro.
      iExists ∅.
      iFrame.
      do 2 (rewrite big_sepM_gset_to_gmap).
      iAssert (([∗ set] k ∈ KVS_keys, ghost_map_elem γ' k (DfracOwn 1%Qp) None) ∗ 
        ([∗ set] k ∈ KVS_keys, ghost_map_elem γ'' k (DfracOwn 1%Qp) None))%I with 
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
      iExists γ', γ'', γ'''.
      iFrame "#".
  Qed.

  Lemma write_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
  Proof.
  Admitted.

  Lemma read_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
  Proof.
  Admitted.

  Lemma commit_implication γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients (res : SI_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_si -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
                     GlobalInvExt commit_test_si T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
  Proof.
  Admitted.

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
      as "[%γmap (Hghost_map_mmap & Hghost_elems_mmap)]".
    iMod (own_alloc (A:=mono_listUR (leibnizO (transaction * state)))
      (●ML [] ⋅ ◯ML [])) as (γexec) "[Hexec_trace _]".
    { 
      apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. 
    }
    iMod (own_log_auth_update _ _ ([] ++ [([], ∅)]) with "[$Hexec_trace]") as "Hexec_trace"; 
      first by apply prefix_app_r.
    iMod (ghost_map_alloc ((gset_to_gmap None clients : gmap socket_address (option (gname * gname * gname * val)))))
      as "[%γsi_name (Hghost_map_msi_name & Hghost_elems_msi_name)]".
    iMod (inv_alloc KVS_InvName ⊤ (∃ T exec, GlobalInvExtSI γmap γexec γsi_name T exec extract clients ∗ 
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
          apply rel_exec_map_init.
        - rewrite /open_transactions_state.
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
    iExists (wrapped_resources γmstate γmlin γmpost γmname γl γmap γexec γsi_name clients res).
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
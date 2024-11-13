From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import user_params aux_defs state_based_model.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !User_params}.

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

  Lemma rev_exists {A : Type} (l : list A) :
    ∃ l', l = rev l'.
  Proof.
    induction l as [|h l IH].
    - exists [].
      by simpl.
    - destruct IH as (l' & Heq). 
      exists (l' ++ [h]).
      rewrite rev_unit.
      set_solver.
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

  Definition rel_exec_map (exec : execution) (m : gmap Key (list val)) :=
    ∃ s, last (split exec).2 = Some s ∧
      (∀ k ov h, s !! k = ov ↔ (m !! k = Some h ∧ last h = ov)) ∧
      (∀ k h, m !! k = Some h → ind_rel_exec_map k exec h).

  Definition reads_from_last_state (exec : execution) (k : Key) (ov : option val) := 
    ∃ s, last (split exec).2 = Some s ∧ s !! k = ov.

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

  Lemma valid_execution_rc_imp exec_pre m_pre exec m s st trans T :
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
      + destruct (Hvalid t Hin) as (s' & Hin_s' & Hcompl & Hno_conf).
        exists s'.
        split_and!.
        * rewrite split_split.
          simpl. 
          set_solver.
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
          assert (read_state c k ov i exec s') as (j & Hleq & Hlookup_j & Hlookup_k);
            first by apply (Hcompl tag c k ov i).
          exists j.
          split_and!; try done.
          rewrite split_split.
          simpl.
          rewrite lookup_app_Some.
          by left.
        * intros i j Hlookup_i Hlookup_j i' t' Hlt Hlookup_i'.
          eapply (Hno_conf i j _ _ i'); try done.
          Unshelve.
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
          -- rewrite split_split in Hlookup_i.
             simpl in Hlookup_i.
             rewrite lookup_app_Some in Hlookup_i.
             destruct Hlookup_i as [Hlookup_i|Hlookup_i]; first done.
             exfalso.
             rewrite split_split in Hlookup_j.
             simpl in Hlookup_j.
             rewrite lookup_app_Some in Hlookup_j.
             rewrite split_length_r in Hlookup_i.
             destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)].
             ++ apply lookup_lt_Some in Hlookup_j.
                rewrite split_length_l in Hlookup_j.
                lia.
             ++ rewrite list_lookup_singleton_Some Nat.sub_0_le in Hlookup_j.
                rewrite split_length_l in Hlookup_j.
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
        exists s_snap.
        assert (s_snap ∈ (split exec).2) as Hsnap_in.
        {
          eapply (elem_of_prefix (split exec_pre).2); try done.
          - apply last_Some_elem_of; set_solver.
          - by apply split_prefix.
        }
        split_and!.
        * rewrite split_split. 
          simpl.
          set_solver.
        * intros tag c key ov i Hlookup_i Hrd_in Hno_writes.
          rewrite /read_state.
          rewrite elem_of_list_lookup in Hsnap_in.
          destruct Hsnap_in as (j & Hsnap_in).
          exists j.
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
             ++ apply lookup_lt_Some in Hsnap_in.
                rewrite split_length_r in Hsnap_in.
                rewrite split_length_l in Hlength_i.
                lia.
             ++ rewrite split_split; simpl.
                rewrite lookup_app_Some; by left.
             ++ rewrite elem_of_app in Hrd_in.
                destruct Hrd_in as [Hrd_in|Hrd_in]; last set_solver.
                assert (reads_from_last_state exec_pre key ov) as (s_snap' & Heq & Hlookup); last set_solver.
                apply (Hreads (tag, c) key ov Hrd_in).
                intros (s' & v' & Hrel).
                apply Hno_writes.
                exists s', v'.
                by apply rel_list_imp.
        * intros i j Hlookup_i Hlookup_j i' t' Hlt Hlookup_i' k (s' & v & Hwr_in) Hwr_in'.
          rewrite elem_of_app in Hwr_in.
          destruct Hwr_in as [Hwr_in|Hwr_in]; last set_solver.
          destruct (Hwrites s' k v Hwr_in) as (h & Hlookup_k & Hlookup_k').
          apply prefix_exists in Hpre.
          destruct Hpre as (exec' & Heq_pre).
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
             assert (i = Init.Nat.pred (length exec_pre)) as Heq_i.
             {
               admit.
             }
             destruct Hlookup_i' as [Hlookup_i'|Hlookup_i'].
             ++ rewrite Heq_pre in Hlookup_i'.
                rewrite split_split in Hlookup_i'.
                simpl in Hlookup_i'.
                rewrite lookup_app_Some in Hlookup_i'.
                destruct Hlookup_i' as [Hlookup_i'|Hlookup_i'].
                ** rewrite Heq_i in Hlt.
                   apply lookup_lt_Some in Hlookup_i'.
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
  Admitted.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources (γmstate : gname) (clients : gset socket_address)
  `(res : !SI_resources Mdl Σ) : SI_resources Mdl Σ :=
    {|
      GlobalInv := True%I;
      OwnMemKey k V := True%I;
      OwnLocalKey k c vo := True%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (s, Some c))%I;
      IsConnected c sa := True%I;
      KVS_si := KVS_si;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (CanStart, None) ∗ ⌜sa ∈ clients⌝)%I;
      KeyUpdStatus v k b := True%I;
      Seen k V := Seen k V%I;
      extract c := res.(snapshot_isolation.specs.resources.extract) c;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Definition trace_inv_name := nroot.@"trinv".

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((SI_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_si ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    SI_spec clients (KVS_wrapped_api lib).
  Proof.
  Admitted.

End trace_proof.
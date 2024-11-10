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
  
  Definition rel_exec_map (exec : execution) (m : gmap Key (list val)) :=
    ∃ s, last (split exec).2 = Some s ∧
      (∀ k ov h, s !! k = ov ↔ (m !! k = Some h ∧ last h = ov)) ∧
      (∀ k h v_i v_j i j, m !! k = Some h → h !! i = Some v_i → h !! j = Some v_j → i < j →
        ∃ s_i' s_j' i' j', (split exec).2 !! i' = Some s_i' ∧ (split exec).2 !! j' = Some s_j' ∧ i' < j') ∧
      (∀ k s_i s_j i j, (split exec).2 !! i = Some s_i → (split exec).2 !! j = Some s_j → i < j → 
        ∃ h v_i' v_j' i' j', m !! k = Some h ∧ h !! i' = Some v_i' ∧ h !! j' = Some v_j' ∧ i' < j').

  Definition reads_from_last_state (exec : execution) (k : Key) (v : val) := 
    ∃ s, last (split exec).2 = Some s ∧ s !! k = Some v.

  Definition GlobalInvExtSI (γ : gname) (T : list transaction) (exec : execution) : iProp Σ := 
    ⌜∀ trans s k v, trans ∈ T → (Rd s k (Some v)) ∈ trans → 
      (¬ ∃ s' v', rel_list trans (Wr s' k v') (Rd s k (Some v))) →
        reads_from_last_state exec k v⌝.

  Lemma valid_execution_rc_imp exec_pre m_pre exec m s st trans T :
    rel_exec_map exec_pre m_pre →
    rel_exec_map exec m →
    exec_pre `prefix_of` exec →
    (∀ s k v, Wr s k v ∈ trans → ∃ h, m_pre !! k = Some h ∧ m !! k = Some h) →
    optional_applied_transaction exec st (trans ++ [Cm s true]) →
    based_on exec T →
    (trans ++ [Cm s true]) ∉ T →
    (∀ s k v, Rd s k (Some v) ∈ trans → 
      (¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k (Some v)))) → 
      reads_from_last_state exec_pre k v) →
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
        * intros tag c k ov i Hlookup_i Hrd_in.
          assert (read_state c k ov i exec s') as (j & Hleq & Hlookup_j & Hlookup_k).
          {
            apply (Hcompl tag c k ov i); last done.
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
          exists j.
          split_and!; try done.
          rewrite split_split.
          simpl.
          rewrite lookup_app_Some.
          by left.
        * intros i j Hlookup_i Hlookup_j i' t' Hlt Hlookup_i'.
          eapply (Hno_conf i j _ _ i'); try done.
          rewrite split_split in Hlookup_i'.
          simpl in Hlookup_i'.
          rewrite lookup_app_Some in Hlookup_i'.
          destruct Hlookup_i' as [Hlookup_i'|Hlookup_i']; first done.
          exfalso.
          rewrite split_split in Hlookup_j.
          simpl in Hlookup_j.
          rewrite lookup_app_Some in Hlookup_j.
          destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)].
          -- apply lookup_lt_Some in Hlookup_j.
             lia.
          -- rewrite list_lookup_singleton_Some Nat.sub_0_le in Hlookup_j.
             lia.
      + assert (t = trans ++ [Cm s true]) as ->; first set_solver.
        destruct Hrel_ex as (s_snap & Hrel_ex).
        exists s_snap.
        split_and!.
        * admit.
        * admit.
        * admit.
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
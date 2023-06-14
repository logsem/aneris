From iris.algebra Require Import gmap.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.aneris_lang.lib Require Import lock_proof map_proof.
Import gen_heap_light.

Definition Key := string.

Section params.

  Class DB_params := {
    DB_addr : socket_address;
    DB_addrs : list (socket_address * socket_address);
    DB_addrs_ips : Forall (λ sa,
                       ip_of_address sa.1 = ip_of_address DB_addr) DB_addrs;
    DB_keys : gset Key;
    DB_serialization : serialization;
    DB_ser_inj : ser_is_injective DB_serialization;
    DB_ser_inj_alt : ser_is_injective_alt DB_serialization;
    DB_inv_name : namespace;
  }.

  Class DBG Σ :=
    {
      DBG_mem :> inG Σ (authR (gen_heapUR Key (option val)));
      DBG_lockG :> lockG Σ;
      DBG_shards : Key → gname;
    }.

  Class DBPreG Σ :=
    {
      DBPreG_mem :> inG Σ (authR (gen_heapUR Key (option val)));
      DBPreG_lockG :> lockG Σ;
    }.

  Definition DBΣ : gFunctors :=
    #[GFunctor (authR (gen_heapUR Key (option val)));
      lockΣ].

  Local Instance subG_DB_preGΣ `{!lockG Σ} : subG DBΣ Σ → DBPreG Σ.
  Proof. solve_inG. Qed.

End params.

Notation DB_Serializable v := (Serializable DB_serialization v).

Record SerializableVal `{!DB_params} :=
  SerVal {SV_val : val;
          SV_ser : DB_Serializable SV_val }.

Coercion SV_val : SerializableVal >-> val.

Existing Instance SV_ser.

Arguments SerVal {_} _ {_}.

Section mem.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Definition mapsto k v := lmapsto (DBG_shards k) k 1 v.

  Notation "k ↦ₖ v" := (mapsto k v) (at level 20).

  Lemma shard_mapsto_valid k v v' : k ↦ₖ v -∗ k ↦ₖ v' -∗ False.
  Proof.
    iIntros "k_v k_v'".
    iPoseProof (lmapsto_agree with "k_v k_v'") as "<-".
    iCombine "k_v k_v'" as "abs".
    by iPoseProof (lmapsto_valid with "abs") as "%abs".
  Qed.

  Definition shard_mem γ shard := gen_heap_light_ctx γ shard.

  Lemma shard_mem_valid γ shard shard' :
    shard_mem γ shard -∗ shard_mem γ shard' -∗ False.
  Proof.
    iIntros "γ_shard γ_shard'".
    iCombine "γ_shard γ_shard'" gives "%abs".
    by apply auth_auth_op_valid in abs.
  Qed.

  Lemma shard_valid γ shard k v :
    ⌜DBG_shards k = γ⌝ -∗
    shard_mem γ shard -∗ k ↦ₖ v -∗ ⌜shard !! k = Some v⌝.
  Proof.
    iIntros (<-) "γ_shard k_v".
    iApply (gen_heap_light_valid with "γ_shard k_v").
  Qed.

  Lemma shard_update γ shard k v v' :
    ⌜DBG_shards k = γ⌝ -∗
    shard_mem γ shard -∗
    k ↦ₖ v ==∗
    shard_mem γ (<[k:=v']> shard) ∗ k ↦ₖ v'.
  Proof.
    iIntros (<-) "γ_shard k_v".
    by iMod (gen_heap_light_update _ _ _ _ v' with "γ_shard k_v").
  Qed.

  Definition shard_lock l ip γ : iProp Σ :=
    ∃ (db : val) (M : gmap Key val) (shard : gmap Key (option val)),
      ⌜is_map db M⌝ ∗ shard_mem γ shard ∗ l ↦[ip] db ∗
      ([∗ set] k ∈ DB_keys, ∀ v, ⌜M !! k = Some v⌝ -∗
                ⌜Serializable DB_serialization v⌝) ∗
      ([∗ set] k ∈ DB_keys, ⌜shard !! k = Some (M !! k)⌝).

End mem.

Notation "k ↦ₖ v" := (mapsto k v) (at level 20).

Section Alloc.

  Context `{!anerisG Mdl Σ, !DB_params, !DBPreG Σ}.

  Lemma pre_alloc_shard :
    ⊢ |==> ∃ γ : gname,
      gen_heap_light_ctx γ (gset_to_gmap None DB_keys) ∗
      ([∗ set] k ∈ DB_keys, lmapsto γ k 1 None).
  Proof.
    iMod (gen_heap_light_init ∅) as "(%γ & Hγ)".
    iInduction DB_keys as [|k keys k_not_key] "Hind" using set_ind_L.
    {
      iModIntro.
      iExists γ.
      iSplitL; last done.
      by rewrite gset_to_gmap_empty.
    }
    iMod ("Hind" with "Hγ") as "(%γ' & own_keys & keys_init)".
    iClear "Hind".
    rewrite gset_to_gmap_union_singleton.
    iMod (gen_heap_light_alloc _ k _ None with "own_keys")
        as "(own_keys & k_init)"; first by apply lookup_gset_to_gmap_None.
    iModIntro.
    iExists γ'.
    iSplitL "own_keys"; first done.
    iApply big_sepS_union; first set_solver.
    iFrame.
    by iApply big_sepS_singleton.
  Qed.

  Lemma pre_alloc_db :
    ⊢ |==> ∃ γs : list gname, ⌜length γs = length DB_addrs⌝ ∗
      ([∗ list] k↦sa ∈ DB_addrs, ∃ γ, ⌜γs !! k = Some γ⌝ ∗
      gen_heap_light_ctx γ (gset_to_gmap None DB_keys)) ∗
      ([∗ list] k↦sa ∈ DB_addrs, ∃ γ, ⌜γs !! k = Some γ⌝ ∗
      ([∗ set] k ∈ DB_keys, lmapsto γ k 1 None)).
  Proof.
    iInduction DB_addrs as [|addr addrs] "Hind" using list_ind.
    {
      iModIntro.
      iExists []; iSplit; first done.
      by iSplit.
    }
    iMod "Hind" as "(%γs & %len_γs & init_● & init_◯)".
    iMod pre_alloc_shard as "(%γ & γ_● & γ_◯)".
    iModIntro.
    iExists (γ :: γs).
    iSplit.
    { iPureIntro. by rewrite/=len_γs. }
    iSplitL "init_● γ_●"; iFrame; iExists γ; by iSplit.
  Qed.

  Lemma alloc_db (hash : Key → nat) :
    (∀ k, k ∈ DB_keys → hash k < length DB_addrs)%nat →
    ⊢ |==> ∃ (dbg : DBG Σ) (γs : list gname), ⌜length γs = length DB_addrs⌝ ∗
      ⌜∀ k γ, γs !! (hash k) = Some γ → DBG_shards k = γ⌝ ∗
      ([∗ list] k↦sa ∈ DB_addrs, ∃ γ, ⌜γs !! k = Some γ⌝ ∗
      shard_mem γ (gset_to_gmap None DB_keys)) ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None).
  Proof.
    move=>hash_valid.
    iMod pre_alloc_db as "(%γs & %len_γs & ●_γs & ◯_γs)".
    iMod (gen_heap_light_init ∅) as "(%default & Hdefault)".
    set (DBPreG_shards (k : Key) := match γs !! (hash k) with
                                  Some γ => γ | None => default end).
    set (dbg := {|
                  DBG_mem := DBPreG_mem;
                  DBG_lockG := DBPreG_lockG;
                  DBG_shards := DBPreG_shards;
                |}).
    iModIntro.
    iExists dbg, γs.
    iFrame.
    iSplit; first done.
    iSplit; first by (iPureIntro; rewrite/=/DBPreG_shards =>k γ ->).
    iInduction DB_keys as [|k keys k_keys] "Hind" using set_ind_L; first done.
    have hash_k : (hash k < length DB_addrs)%nat
              by apply hash_valid; set_solver.
    move: (lookup_lt_is_Some_2 _ _ hash_k)=>[sa addrs_k].
    iPoseProof (big_sepL_lookup_acc_impl (hash k) _ addrs_k with "◯_γs")
            as "((%γ & %k_γ & ◯_γ) & lookup)".
    iPoseProof (big_sepS_insert _ _ _ k_keys with "◯_γ") as "(◯_γ & ◯_keys)".
    iApply (big_sepS_insert_2 with "[◯_γ]");
        first by have <- : (DBG_shards k) = γ by rewrite/=/DBPreG_shards k_γ.
    iPoseProof ("lookup" $! (λ i sa, (∃ γ0 : gname,
         ⌜γs !! i = Some γ0⌝ ∗ ([∗ set] k1 ∈ keys, lmapsto γ0 k1 1 None))%I)
          with "[] [◯_keys]") as "◯_keys".
    {
      iModIntro.
      iIntros (i ? ? i_shards) "(%γ' & %i_γ' & ◯_γ')".
      iPoseProof (big_sepS_insert _ _ _ k_keys with "◯_γ'") as "(_ & ◯_γ')".
      iExists γ'.
      by iFrame.
    }
    { iExists γ. by iFrame. }
    iApply ("Hind" with "[] ◯_keys"); last done.
    iPureIntro=>k' k'_keys.
    apply hash_valid.
    set_solver.
  Qed.

End Alloc.

Section user_params.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Definition write_ser := prod_serialization string_serialization DB_serialization.

  Definition read_ser := string_serialization.

  Definition req_ser := sum_serialization write_ser read_ser.

  Definition rep_ser := sum_serialization unit_serialization
                            (option_serialization DB_serialization).

  Definition ReqData : Type := (coPset * (iProp Σ) * (iProp Σ) * Key *
                                  SerializableVal) +
              (coPset * (iProp Σ) * (option val → iProp Σ) * Key).

  Definition RepData : Type := True.

  Lemma write_ser_is_ser_injective :
    ser_is_injective write_ser.
  Proof.
    apply prod_ser_is_ser_injective;
      [apply string_ser_is_ser_injective|apply DB_ser_inj].
  Qed.

  Lemma write_ser_is_ser_injective_alt :
    ser_is_injective_alt write_ser.
  Proof.
    apply prod_ser_is_ser_injective_alt;
      [apply string_ser_is_ser_injective_alt|apply DB_ser_inj_alt].
  Qed.

  Definition read_ser_is_ser_injective := string_ser_is_ser_injective.

  Definition read_ser_is_ser_injective_alt := string_ser_is_ser_injective_alt.

  Lemma unit_ser_is_ser_injective : ser_is_injective unit_serialization.
  Proof.
    by move=>s v1 v2[->->][->_].
  Qed.

  Lemma unit_ser_is_ser_injective_alt : ser_is_injective_alt unit_serialization.
  Proof.
    by move=>s1 s2 v[->->][_->].
  Qed.

  Lemma option_ser_is_ser_injective : ser_is_injective
    (option_serialization DB_serialization).
  Proof.
    move=>s v1 v2[[->->][[->_]|[w][sw][->][_]]|[w][sw][->][ser_w->/=
            [[->]|[w'][sw'][->][ser_w'][sw_sw']]]]//.
    by move:sw_sw' ser_w ser_w'=>->h/(DB_ser_inj _ _ _ h)->.
  Qed.

  Lemma option_ser_is_ser_injective_alt : ser_is_injective_alt
    (option_serialization DB_serialization).
  Proof.
    by move=>s1 s2 v[[->->][[_->]|[w][sw][]]|[w][sw][->][ser_w]->/=
            [[]|[w'][sw'][][<-][]/(DB_ser_inj_alt _ _ _ ser_w)->]].
  Qed.

  Lemma req_ser_is_ser_injective : ser_is_injective req_ser.
  Proof.
    apply sum_ser_is_ser_injective;
      [apply write_ser_is_ser_injective|apply read_ser_is_ser_injective].
  Qed.

  Lemma req_ser_is_ser_injective_alt : ser_is_injective_alt req_ser.
  Proof.
    apply sum_ser_is_ser_injective_alt;
      [apply write_ser_is_ser_injective_alt|apply read_ser_is_ser_injective_alt].
  Qed.

  Lemma rep_ser_is_ser_injective : ser_is_injective rep_ser.
  Proof.
    apply sum_ser_is_ser_injective;
      [apply unit_ser_is_ser_injective|apply option_ser_is_ser_injective].
  Qed.

  Lemma rep_ser_is_ser_injective_alt : ser_is_injective_alt rep_ser.
  Proof.
    apply sum_ser_is_ser_injective_alt;
      [apply unit_ser_is_ser_injective_alt|apply option_ser_is_ser_injective_alt].
  Qed.

  Definition ReqPre (req : val) (data : ReqData) : iProp Σ :=
    (∃ E P Q (k : Key) (v : SerializableVal), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗
      ⌜req = InjLV (#k, v)%V⌝ ∗ ⌜data = inl (E, P, Q, k, v)⌝ ∗ P ∗
      □ (P ={⊤, E}=∗ ∃ old, k ↦ₖ old ∗ ▷(k ↦ₖ Some (SV_val v) ={E, ⊤}=∗ Q))) ∨
     (∃ E P Q (k : Key), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗ ⌜req = InjRV #k⌝ ∗
      ⌜data = inr (E, P, Q, k)⌝ ∗ P ∗
      □ (P ={⊤, E}=∗ ∃ v, k ↦ₖ v ∗ ▷ (k ↦ₖ v ={E,⊤}=∗ Q v))).

  Definition ReqPost (rep : val) (data : ReqData) (_ : RepData) : iProp Σ :=
    (∃ E P (Q : iProp Σ) (k : Key) (v : SerializableVal), Q ∗
      ⌜rep = InjLV #()⌝ ∗ ⌜data = inl (E, P, Q, k, v)⌝) ∨
    (∃ E P Q (k : Key), ⌜data = inr (E, P, Q, k)⌝ ∗
      ((∃ v : SerializableVal, ⌜rep = InjRV (SOMEV v)⌝ ∗ Q (Some (SV_val v))) ∨
      (⌜rep = InjRV NONEV⌝ ∗ Q None))).

  Global Instance user_params_at_server : MTS_user_params :=
    {|
      MTS_req_ser := req_ser;
      MTS_req_ser_inj := req_ser_is_ser_injective;
      MTS_req_ser_inj_alt := req_ser_is_ser_injective_alt;
      MTS_req_data := ReqData;
      MTS_rep_ser := rep_ser;
      MTS_rep_ser_inj := rep_ser_is_ser_injective;
      MTS_rep_ser_inj_alt := rep_ser_is_ser_injective_alt;
      MTS_rep_data := RepData;
      MTS_saddr := DB_addr;
      MTS_mN := (DB_inv_name .@ "server");
      MTS_handler_pre := ReqPre;
      MTS_handler_post := ReqPost;
    |}.

  Definition shardReqPre γ (req : val) (data : ReqData) : iProp Σ :=
    (∃ E P Q (k : Key) (v : SerializableVal), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗
      ⌜req = InjLV (#k, v)%V⌝ ∗ ⌜data = inl (E, P, Q, k, v)⌝ ∗ P ∗ ⌜DBG_shards k = γ⌝ ∗
      □ (P ={⊤, E}=∗ ∃ old, k ↦ₖ old ∗ ▷(k ↦ₖ Some (SV_val v) ={E, ⊤}=∗ Q))) ∨
     (∃ E P Q (k : Key), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗ ⌜req = InjRV #k⌝ ∗
      ⌜data = inr (E, P, Q, k)⌝ ∗ P ∗ ⌜DBG_shards k = γ⌝ ∗
      □ (P ={⊤, E}=∗ ∃ v, k ↦ₖ v ∗ ▷ (k ↦ₖ v ={E,⊤}=∗ Q v))).

  Global Instance user_params_at_shard γ sa : MTS_user_params :=
    {|
      MTS_req_ser := req_ser;
      MTS_req_ser_inj := req_ser_is_ser_injective;
      MTS_req_ser_inj_alt := req_ser_is_ser_injective_alt;
      MTS_req_data := ReqData;
      MTS_rep_ser := rep_ser;
      MTS_rep_ser_inj := rep_ser_is_ser_injective;
      MTS_rep_ser_inj_alt := rep_ser_is_ser_injective_alt;
      MTS_rep_data := RepData;
      MTS_saddr := sa;
      MTS_mN := (DB_inv_name .@ "shard");
      MTS_handler_pre := shardReqPre γ;
      MTS_handler_post := ReqPost;
    |}.

End user_params.
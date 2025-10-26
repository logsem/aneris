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
Import inject.

Section params.

  (** Abstract parameters of the database *)

  Class DB_params := {
    (** The type of the keys *)
    Key : Type;
    DB_keys_val :> Inject Key val;
    DB_key_eq_dec :> EqDecision Key;
    DB_key_countable :> Countable Key;

    (** The type of the values *)
    Val : Type;
    DB_vals_val :> Inject Val val;

    (** The database's address *)
    DB_addr : socket_address;

    (** The shard's addresses *)
    DB_addrs : list (socket_address * socket_address);
    DB_addrs_ips : Forall (λ sa,
                       ip_of_address sa.1 = ip_of_address DB_addr) DB_addrs;

    (** The database's keys *)
    DB_keys : gset Key;

    (** The key redistribution function *)
    DB_hash : Key → nat;
    DB_hash_valid (k : Key) : (DB_hash k < length DB_addrs)%nat;

    (** Some serialization lemmas *)
    DB_key_ser : serialization;
    DB_val_ser : serialization;
    DB_key_ser_inj : ser_is_injective DB_key_ser;
    DB_key_ser_inj_alt : ser_is_injective_alt DB_key_ser;
    DB_val_ser_inj : ser_is_injective DB_val_ser;
    DB_val_ser_inj_alt : ser_is_injective_alt DB_val_ser;
    DB_keys_serializable (k : Key) :> Serializable DB_key_ser $k;
    DB_vals_serializable (v : Val) :> Serializable DB_val_ser $v;

    (** The namespace for invariants *)
    DB_inv_name : namespace;
  }.

  Context `{!DB_params}.

  (** Information for ghost states *)
  Class DBG Σ :=
    {
      DBG_mem :> inG Σ (authR (gen_heapUR Key (option Val)));
      DBG_lockG :> lockG Σ;
      DBG_hash : Key → gname;
    }.

  (** Information for ghost states needed for instantiation *)
  Class DBPreG Σ :=
    {
      DBPreG_mem :> inG Σ (authR (gen_heapUR Key (option Val)));
      DBPreG_lockG :> lockG Σ;
    }.

  Definition DBΣ : gFunctors :=
    #[GFunctor (authR (gen_heapUR Key (option Val)));
      lockΣ].

  Local Instance subG_DBPreGΣ `{!lockG Σ} : subG DBΣ Σ → DBPreG Σ.
  Proof. solve_inG. Qed.

End params.

Section mem.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Definition mapsto k vo := lmapsto (DBG_hash k) k 1 vo.

  Notation "k ↦ₖ vo" := (mapsto k vo) (at level 20).

  Lemma shard_mapsto_valid k vo vo' : k ↦ₖ vo -∗ k ↦ₖ vo' -∗ False.
  Proof.
    iIntros "k_vo k_vo'".
    iPoseProof (lmapsto_agree with "k_vo k_vo'") as "<-".
    iCombine "k_vo k_vo'" as "abs".
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

  Lemma shard_valid γ shard k vo :
    ⌜DBG_hash k = γ⌝ -∗
    shard_mem γ shard -∗ k ↦ₖ vo -∗ ⌜shard !! k = Some vo⌝.
  Proof.
    iIntros (<-) "γ_shard k_vo".
    iApply (gen_heap_light_valid with "γ_shard k_vo").
  Qed.

  Lemma shard_update γ shard k vo vo' :
    ⌜DBG_hash k = γ⌝ -∗
    shard_mem γ shard -∗
    k ↦ₖ vo ==∗
    shard_mem γ (<[k:=vo']> shard) ∗ k ↦ₖ vo'.
  Proof.
    iIntros (<-) "γ_shard k_vo".
    by iMod (gen_heap_light_update _ _ _ _ vo' with "γ_shard k_vo").
  Qed.

  Definition shard_lock l ip γ : iProp Σ :=
    ∃ (db : val) (M : gmap Key Val) (shard : gmap Key (option Val)),
      ⌜is_map db M⌝ ∗ shard_mem γ shard ∗ l ↦[ip] db ∗
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
      ([∗ list] k ↦ sa ∈ DB_addrs, ∃ γ, ⌜γs !! k = Some γ⌝ ∗
          gen_heap_light_ctx γ (gset_to_gmap None DB_keys)) ∗
      ([∗ list] γ ∈ γs, ([∗ set] k ∈ DB_keys, lmapsto γ k 1 None)).
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

  (** Provides the information needed to initialize the database *)
  Lemma alloc_db :
    ⊢ |==> ∃ (dbg : DBG Σ) (γs : list gname), ⌜length γs = length DB_addrs⌝ ∗
      ⌜∀ k γ, γs !! (DB_hash k) = Some γ → DBG_hash k = γ⌝ ∗
      ([∗ list] i ↦ sa ∈ DB_addrs, ∃ γ, ⌜γs !! i = Some γ⌝ ∗
          shard_mem γ (gset_to_gmap None DB_keys)) ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None).
  Proof.
    iMod pre_alloc_db as "(%γs & %len_γs & ●_γs & ◯_γs)".
    iMod (gen_heap_light_init ∅) as "(%default & Hdefault)".
    set (hash (k : Key) := match γs !! (DB_hash k) with
                                  Some γ => γ | None => default end).
    set (dbg := {|
                  DBG_mem := DBPreG_mem;
                  DBG_lockG := DBPreG_lockG;
                  DBG_hash := hash;
                |}).
    iModIntro.
    iExists dbg, γs.
    iFrame "∗%".
    iSplit; first by (iPureIntro; rewrite/=/hash =>k γ ->).
    iInduction DB_keys as [|k keys k_keys] "Hind" using set_ind_L; first done.
    move: (DB_hash_valid k).
    rewrite -len_γs=>/(lookup_lt_is_Some_2 _ _)=>[][γ γ_k].
    iPoseProof (big_sepL_lookup_acc_impl (DB_hash k) _ γ_k with "◯_γs")
            as "(◯_γ & lookup)".
    iPoseProof (big_sepS_insert _ _ _ k_keys with "◯_γ") as "(◯_γ & ◯_keys)".
    iApply (big_sepS_insert_2 with "[◯_γ]");
        first by have <- : (DBG_hash k) = γ by rewrite/=/hash γ_k.
    iPoseProof ("lookup" $! (λ i γ0, [∗ set] k1 ∈ keys, lmapsto γ0 k1 1 None)%I
          with "[] ◯_keys") as "◯_keys".
    {
      iModIntro.
      iIntros (i γ' i_γ' i_k) "◯_γ'".
      by iPoseProof (big_sepS_insert _ _ _ k_keys with "◯_γ'") as "(_ & ◯_γ')".
    }
    iApply ("Hind" with "◯_keys Hdefault").
  Qed.

End Alloc.

Section user_params.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Definition write_ser := prod_serialization DB_key_ser DB_val_ser.

  Definition read_ser := DB_key_ser.

  Definition req_ser := sum_serialization write_ser read_ser.

  Definition rep_ser := sum_serialization unit_serialization
                            (option_serialization DB_val_ser).

  Definition ReqData : Type := (coPset * (iProp Σ) * Key * Val) +
              (coPset * (option Val → iProp Σ) * Key).

  Definition RepData : Type := True.

  Lemma write_ser_is_ser_injective :
    ser_is_injective write_ser.
  Proof.
    apply prod_ser_is_ser_injective;
      [apply DB_key_ser_inj|apply DB_val_ser_inj].
  Qed.

  Lemma write_ser_is_ser_injective_alt :
    ser_is_injective_alt write_ser.
  Proof.
    apply prod_ser_is_ser_injective_alt;
      [apply DB_key_ser_inj_alt|apply DB_val_ser_inj_alt].
  Qed.

  Lemma unit_ser_is_ser_injective : ser_is_injective unit_serialization.
  Proof.
    by move=>s v1 v2[->->][->_].
  Qed.

  Lemma unit_ser_is_ser_injective_alt : ser_is_injective_alt unit_serialization.
  Proof.
    by move=>s1 s2 v[->->][_->].
  Qed.

  Lemma option_ser_is_ser_injective : ser_is_injective
    (option_serialization DB_val_ser).
  Proof.
    move=>s v1 v2[[->->][[->_]|[w][sw][->][_]]|[w][sw][->][ser_w->/=
            [[->]|[w'][sw'][->][ser_w'][sw_sw']]]]//.
    by move:sw_sw' ser_w ser_w'=>->h/(DB_val_ser_inj _ _ _ h)->.
  Qed.

  Lemma option_ser_is_ser_injective_alt : ser_is_injective_alt
    (option_serialization DB_val_ser).
  Proof.
    by move=>s1 s2 v[[->->][[_->]|[w][sw][]]|[w][sw][->][ser_w]->/=
            [[]|[w'][sw'][][<-][]/(DB_val_ser_inj_alt _ _ _ ser_w)->]].
  Qed.

  Lemma req_ser_is_ser_injective : ser_is_injective req_ser.
  Proof.
    apply sum_ser_is_ser_injective;
      [apply write_ser_is_ser_injective|apply DB_key_ser_inj].
  Qed.

  Lemma req_ser_is_ser_injective_alt : ser_is_injective_alt req_ser.
  Proof.
    apply sum_ser_is_ser_injective_alt;
      [apply write_ser_is_ser_injective_alt|apply DB_key_ser_inj_alt].
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
    (∃ E Q (k : Key) (v : Val), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗
      ⌜req = InjLV ($k, $v)%V⌝ ∗ ⌜data = inl (E, Q, k, v)⌝ ∗
      (|={⊤, E}=> ▷ ∃ old, k ↦ₖ old ∗ (k ↦ₖ Some v ={E, ⊤}=∗ Q))) ∨
     (∃ E Q (k : Key), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗ ⌜req = InjRV $k⌝ ∗
      ⌜data = inr (E, Q, k)⌝ ∗
      (|={⊤, E}=> ▷ ∃ v, k ↦ₖ v ∗ (k ↦ₖ v ={E,⊤}=∗ Q v))).

  Definition ReqPost (rep : val) (data : ReqData) (_ : RepData) : iProp Σ :=
    (∃ E (Q : iProp Σ) (k : Key) (v : Val), Q ∗
      ⌜rep = InjLV #()⌝ ∗ ⌜data = inl (E, Q, k, v)⌝) ∨
    (∃ E Q (k : Key), ⌜data = inr (E, Q, k)⌝ ∗
      (∃ vo : option Val, ⌜rep = InjRV $vo⌝ ∗ Q vo)).

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
    (∃ E Q (k : Key) (v : Val), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗
      ⌜req = InjLV ($k, $v)%V⌝ ∗ ⌜data = inl (E, Q, k, v)⌝ ∗ ⌜DBG_hash k = γ⌝ ∗
      (|={⊤, E}=> ▷ ∃ old, k ↦ₖ old ∗ (k ↦ₖ Some v ={E, ⊤}=∗ Q))) ∨
     (∃ E Q (k : Key), ⌜↑DB_inv_name ⊆ E⌝ ∗ ⌜k ∈ DB_keys⌝ ∗ ⌜req = InjRV $k⌝ ∗
      ⌜data = inr (E, Q, k)⌝ ∗ ⌜DBG_hash k = γ⌝ ∗
      (|={⊤, E}=> ▷ ∃ v, k ↦ₖ v ∗ (k ↦ₖ v ={E,⊤}=∗ Q v))).

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

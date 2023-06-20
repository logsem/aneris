From aneris.examples.snapshot_isolation.util.util_deprecated Require Import util_code.
From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Import time events resources_points_to_with_key_status specs_points_to_with_key_status.

From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From iris.algebra Require Import gmap.

Section proof.

  Context `{!anerisG Mdl Σ, !User_params, !KVS_time, !KVSG Σ,
                !SI_resources Mdl Σ}.

  Lemma commitU_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    commit_spec -∗
    <<< ∀∀ (m ms: gmap Key (option write_event))
           (mc : gmap Key (option val * bool)),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitU c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        ((⌜can_commit m ms mc⌝ ∗
         ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
          ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo)) ∨
        (** Transaction has been aborted. *)
         (⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo)) >>>.
  Proof.
    iIntros (cst sa E name) "#commit %Φ!>HΦ".
    rewrite/commitU.
    wp_pures.
    wp_apply ("commit" with "[//] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & pre & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [( _ & post)|(_ & post)])".
    {
      iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
      iModIntro.
      by wp_pures.
    }
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
    iModIntro.
    by wp_pures.
  Qed.

  Lemma commitT_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    commit_spec -∗
    <<< ∀∀ (m ms: gmap Key (option write_event))
           (mc : gmap Key (option val * bool)),
        ⌜can_commit m ms mc⌝ ∗
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitT c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
         ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
          ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo) >>>.
  Proof.
    iIntros (cst sa E name) "#commit %Φ !>HΦ".
    rewrite/commitT/assert.
    wp_pures.
    wp_apply ("commit" with "[//] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & (%can_commit & pre) & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [(-> & _ & post)|(_ & %abs & _)])";
          last by move: (abs can_commit).
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
    iModIntro.
    by wp_pures.
  Qed.

  Lemma simplified_wait_on_key_spec :
    ∀ (cst cond : val) sa (k : Key) E (P : iProp Σ) (Q : val → iProp Σ) ms,
    ⌜k ∈ KVS_keys⌝ -∗
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    start_spec -∗
    read_spec -∗
    commit_spec -∗
    (∀ v, {{{ P }}} cond v @[ip_of_address sa]
          {{{ b, RET #b; (⌜b = true⌝ ∗ Q v) ∨ (⌜b = false⌝ ∗ P) }}}) -∗
    (□|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
                  ▷ (([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ={E, ⊤}=∗ emp)) -∗
    {{{
      P ∗
      ConnectionState cst (Active ms) ∗
      ([∗ map] k ↦ eo ∈ ms, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}
      (rec: "aux" <> :=
      match: snapshot_isolation_code.read cst #k with
        InjL <> =>
          commitU cst ;; snapshot_isolation_code.start cst ;; "aux" #()
      | InjR "v" =>
        if: cond "v"
        then commitU cst ;; snapshot_isolation_code.start cst
        else commitU cst ;; 
             snapshot_isolation_code.start cst ;; "aux" #()
      end)%V #() @[ip_of_address sa]
    {{{ v m, RET #(); Q v ∗
        ⌜dom m = dom ms⌝ ∗
        ConnectionState cst (Active m) ∗
        ([∗ map] k ↦ eo ∈ m, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}.
  Proof.
    iIntros (cst cond sa k E P Q ms k_keys name k_ms) "#start #read #commit
            #cond_spec #inv %Φ !>(P & Active & cache) HΦ".
    wp_pures.
    iRevert (ms k_ms) "inv HΦ cache Active P".
    iLöb as "IH".
    iIntros (ms k_ms) "#inv HΦ cache Active P".
    destruct (proj1 (elem_of_dom ms k) k_ms) as (v & ms_k).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ ms_k with "cache")
          as "((k_v & updated) & cache)".
    wp_apply ("read" with "[//] k_v").
    iIntros "k_v".
    iSpecialize ("cache" with "[$k_v $updated]").
    clear ms_k.
    case: v=>[w|]; last first.
    {
      wp_pures.
      wp_apply (commitU_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        iSplit; first done.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      {
        iDestruct "post" as "[(_ & (%t & _ & post))|(_ & post)]"; last iFrame.
        iPoseProof (big_sepM2_fmap_r _ _ _ ms with "post") as "post".
        iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "post []")
            as "post".
        {
          iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
          by case: (weo_val w2)=>[?|]; iSplit.
        }
        iPoseProof (big_sepM2_sepM with "post") as "(post & _)"; last done.
        move=>{k_keys k_ms} k.
        by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
        apply elem_of_dom;
        move: k_dom;
        rewrite m_ms.
      }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms in k_ms.
      rewrite -m_ms.
      by iApply ("IH" with "[//] inv HΦ snap Active").
    }
    wp_pures.
    wp_apply ("cond_spec" with "P").
    iIntros "% [(-> & Q)|(-> & P)]".
    {
      wp_pures.
      wp_apply (commitU_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        iSplit; first done.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      {
        iDestruct "post" as "[(_ & (%t & _ & post))|(_ & post)]"; last iFrame.
        iPoseProof (big_sepM2_fmap_r _ _ _ ms with "post") as "post".
        iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "post []")
            as "post".
        {
          iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
          by case: (weo_val w2)=>[?|]; iSplit.
        }
        iPoseProof (big_sepM2_sepM with "post") as "(post & _)"; last done.
        move=>{k_keys k_ms} k.
        by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
        apply elem_of_dom;
        move: k_dom;
        rewrite m_ms.
      }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms in k_ms.
      rewrite -m_ms.
      by iApply ("HΦ" with "[$Q $Active $snap]").
    }
    wp_pures.
    wp_apply (commitU_spec with "[//] commit").
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
    iSplitL "Active m_kvs cache".
    {
      iFrame.
      iSplit; first done.
      iSplit; first by rewrite dom_fmap_L.
      by iApply big_sepM_fmap.
    }
    iIntros "!>(CanStart & post)".
    iMod ("close" with "[post]") as "_".
    {
      iDestruct "post" as "[(_ & (%t & _ & post))|(_ & post)]"; last iFrame.
      iPoseProof (big_sepM2_fmap_r _ _ _ ms with "post") as "post".
      iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "post []")
          as "post".
      {
        iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
        by case: (weo_val w2)=>[?|]; iSplit.
      }
      iPoseProof (big_sepM2_sepM with "post") as "(post & _)"; last done.
      move=>{k_keys k_ms} k.
      by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
      apply elem_of_dom;
      move: k_dom;
      rewrite m_ms.
    }
    iModIntro.
    wp_pures.
    wp_apply ("start" $! _ _ E with "[//]").
    clear m m_ms.
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m.
    iSplitL "CanStart m_kvs"; first iFrame.
    iIntros "!>(Active & m_kvs & snap)".
    iMod ("close" with "[$m_kvs]") as "_".
    iModIntro.
    wp_pures.
    rewrite -m_ms in k_ms.
    rewrite -m_ms.
    by iApply ("IH" with "[//] inv HΦ snap Active").
  Qed.

   Lemma wait_on_key_spec :
    ∀ (cst cond : val) sa (k : Key) E (P : iProp Σ) (Q : val → iProp Σ) ms mc,
    ⌜k ∈ KVS_keys⌝ -∗
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ dom mc⌝ -∗
    ⌜dom ms = dom mc⌝ -∗
    start_spec -∗
    read_spec -∗
    commit_spec -∗
    (∀ v, {{{ P }}} cond v @[ip_of_address sa]
          {{{ b, RET #b; (⌜b = true⌝ ∗ Q v) ∨ (⌜b = false⌝ ∗ P) }}}) -∗
    (□|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
                  ▷ (⌜can_commit m ms mc⌝ ∗ (∃ t, ⌜max_timestamp t m⌝ ∗
                      ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo)) ∨
                    ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo)
                    ={E, ⊤}=∗ emp)) -∗
    {{{
      P ∗
      ConnectionState cst (Active ms) ∗
      ([∗ map] k ↦ p ∈ mc, k ↦{cst} p.1  ∗ KeyUpdStatus cst k p.2)
    }}}
      wait_on_key cst cond #k @[ip_of_address sa]
    {{{ v m, RET #(); Q v ∗
        ⌜dom m = dom ms⌝ ∗
        ConnectionState cst (Active m) ∗
        ([∗ map] k ↦ eo ∈ m, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}.
  Proof.
    iIntros (cst cond sa k E P Q ms mc k_keys name k_mc ms_mc) "#start #read
       #commit #cond_spec #inv !>%Φ (P & Active & cache) HΦ".
    rewrite/wait_on_key.
    wp_pures.
    destruct (proj1 (elem_of_dom mc k) k_mc) as ([v b] & mc_k).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ mc_k with "cache")
          as "((k_v & updated) & cache)".
    clear mc_k.
    wp_apply ("read" with "[//] k_v").
    iIntros "k_v".
    iSpecialize ("cache" with "[$k_v $updated]").
    case: v=>[w|]; last first.
    {
      wp_pures.
      wp_apply (commitU_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, mc.
      iSplitL "Active m_kvs cache".
      { iFrame. by iSplit. }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      { iDestruct "post" as "[post|(_ & post)]"; iFrame. }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      do 2 (wp_pure _).
      rewrite -ms_mc -m_ms in k_mc.
      rewrite -m_ms.
      wp_apply (simplified_wait_on_key_spec with "[//] [//] [//] start read
            commit cond_spec [] [$P $Active $snap]"); last done.
      iModIntro.
      iMod "inv" as "(%m' & %m_m' & snap & close)".
      iModIntro.
      iExists m'.
      iSplit; first done.
      iFrame.
      iIntros "!>snap".
      iMod ("close" with "[$snap]").
      by iModIntro.
    }
    wp_pures.
    wp_apply ("cond_spec" with "P").
    iIntros "% [(-> & Q)|(-> & P)]".
    {
      wp_pures.
      wp_apply (commitU_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, mc.
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        by iSplit.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      { iDestruct "post" as "[post|(_ & post)]"; iFrame. }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -ms_mc -m_ms in k_mc.
      rewrite -m_ms.
      by iApply ("HΦ" with "[$Q $Active $snap]").
    }
    wp_pures.
    wp_apply (commitU_spec with "[//] commit").
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "Active m_kvs cache".
    {
      iFrame.
      by iSplit.
    }
    iIntros "!>(CanStart & post)".
    iMod ("close" with "[post]") as "_".
    { iDestruct "post" as "[post|(_ & post)]"; iFrame. }
    iModIntro.
    wp_pures.
    wp_apply ("start" $! _ _ E with "[//]").
    clear m m_ms.
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m.
    iSplitL "CanStart m_kvs"; first iFrame.
    iIntros "!>(Active & m_kvs & snap)".
    iMod ("close" with "[$m_kvs]") as "_".
    iModIntro.
    do 2 (wp_pure _).
    rewrite -ms_mc -m_ms in k_mc.
    rewrite -m_ms.
    wp_apply (simplified_wait_on_key_spec with "[//] [//] [//] start read
            commit cond_spec [] [$P $Active $snap]"); last done.
    iModIntro.
    iMod "inv" as "(%m' & %m_m' & snap & close)".
    iModIntro.
    iExists m'.
    iSplit; first done.
    iFrame.
    iIntros "!>snap".
    iMod ("close" with "[$snap]").
    by iModIntro.
  Qed.

  Lemma simplified_wait_on_keyT_spec :
    ∀ (cst cond : val) sa (k : Key) E (P : iProp Σ) (Q : val → iProp Σ) ms,
    ⌜k ∈ KVS_keys⌝ -∗
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    start_spec -∗
    read_spec -∗
    commit_spec -∗
    (∀ v, {{{ P }}} cond v @[ip_of_address sa]
          {{{ b, RET #b; (⌜b = true⌝ ∗ Q v) ∨ (⌜b = false⌝ ∗ P) }}}) -∗
    (□|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
                  ▷ (([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ={E, ⊤}=∗ emp)) -∗
    {{{
      P ∗
      ConnectionState cst (Active ms) ∗
      ([∗ map] k ↦ eo ∈ ms, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}
      (rec: "aux" <> :=
      match: snapshot_isolation_code.read cst #k with
        InjL <> =>
          commitT cst ;; snapshot_isolation_code.start cst ;; "aux" #()
      | InjR "v" =>
        if: cond "v"
        then commitT cst ;; snapshot_isolation_code.start cst
        else commitT cst ;; 
             snapshot_isolation_code.start cst ;; "aux" #()
      end)%V #() @[ip_of_address sa]
    {{{ v m, RET #(); Q v ∗
        ⌜dom m = dom ms⌝ ∗
        ConnectionState cst (Active m) ∗
        ([∗ map] k ↦ eo ∈ m, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}.
  Proof.
    iIntros (cst cond sa k E P Q ms k_keys name k_ms) "#start #read #commit
            #cond_spec #inv %Φ !>(P & Active & cache) HΦ".
    wp_pures.
    iRevert (ms k_ms) "inv HΦ cache Active P".
    iLöb as "IH".
    iIntros (ms k_ms) "#inv HΦ cache Active P".
    destruct (proj1 (elem_of_dom ms k) k_ms) as (v & ms_k).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ ms_k with "cache")
          as "((k_v & updated) & cache)".
    wp_apply ("read" with "[//] k_v").
    iIntros "k_v".
    iSpecialize ("cache" with "[$k_v $updated]").
    clear ms_k.
    case: v=>[w|]; last first.
    {
      wp_pures.
      wp_apply (commitT_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        iSplit.
        {
          iPureIntro.
          move=>k' v.
          rewrite lookup_fmap.
          by case : (ms !! k').
        }
        iSplit; first done.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      {
        iDestruct "post" as "(%t & %timestamp & snap)".
        iPoseProof (big_sepM2_fmap_r _ _ _ ms with "snap") as "snap".
        iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "snap []")
            as "snap".
        {
          iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
          by case: (weo_val w2)=>[?|]; iSplit.
        }
        iPoseProof (big_sepM2_sepM with "snap") as "(snap & _)"; last done.
        move=>{k_keys k_ms} k.
        by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
        apply elem_of_dom;
        move: k_dom;
        rewrite m_ms.
      }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms in k_ms.
      rewrite -m_ms.
      by iApply ("IH" with "[//] inv HΦ snap Active").
    }
    wp_pures.
    wp_apply ("cond_spec" with "P").
    iIntros "% [(-> & Q)|(-> & P)]".
    {
      wp_pures.
      wp_apply (commitT_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        iSplit.
        {
          iPureIntro.
          move=>k' v.
          rewrite lookup_fmap.
          by case : (ms !! k').
        }
        iSplit; first done.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[post]") as "_".
      {
        iDestruct "post" as "(%t & %timestamp & post)"; last iFrame.
        iPoseProof (big_sepM2_fmap_r _ _ _ ms with "post") as "post".
        iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "post []")
            as "post".
        {
          iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
          by case: (weo_val w2)=>[?|]; iSplit.
        }
        iPoseProof (big_sepM2_sepM with "post") as "(post & _)"; last done.
        move=>{k_keys k_ms} k.
        by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
        apply elem_of_dom;
        move: k_dom;
        rewrite m_ms.
      }
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms in k_ms.
      rewrite -m_ms.
      by iApply ("HΦ" with "[$Q $Active $snap]").
    }
    wp_pures.
    wp_apply (commitT_spec with "[//] commit").
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m, ms, ((λ eo, (weo_val eo, false)) <$> ms).
    iSplitL "Active m_kvs cache".
    {
      iFrame.
      iSplit.
      {
        iPureIntro.
        move=>k' v.
        rewrite lookup_fmap.
        by case : (ms !! k').
      }
      iSplit; first done.
      iSplit; first by rewrite dom_fmap_L.
      by iApply big_sepM_fmap.
    }
    iIntros "!>(CanStart & post)".
    iMod ("close" with "[post]") as "_".
    {
      iDestruct "post" as "(%t & %timestamp & post)"; last iFrame.
      iPoseProof (big_sepM2_fmap_r _ _ _ ms with "post") as "post".
      iPoseProof (big_sepM2_impl _ (λ k w1 w2, k ↦ₖ w1 ∗ emp)%I with "post []")
          as "post".
      {
        iIntros "!>" (k' w1 w2 m_k' ms_k') "k_w1".
        by case: (weo_val w2)=>[?|]; iSplit.
      }
      iPoseProof (big_sepM2_sepM with "post") as "(post & _)"; last done.
      move=>{k_keys k_ms} k.
      by split=>[]/(proj2 (elem_of_dom _ _)) k_dom;
      apply elem_of_dom;
      move: k_dom;
      rewrite m_ms.
    }
    iModIntro.
    wp_pures.
    wp_apply ("start" $! _ _ E with "[//]").
    clear m m_ms.
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & m_kvs & close)".
    iModIntro.
    iExists m.
    iSplitL "CanStart m_kvs"; first iFrame.
    iIntros "!>(Active & m_kvs & snap)".
    iMod ("close" with "[$m_kvs]") as "_".
    iModIntro.
    wp_pures.
    rewrite -m_ms in k_ms.
    rewrite -m_ms.
    by iApply ("IH" with "[//] inv HΦ snap Active").
  Qed.


   Lemma wait_on_keyT_spec :
    ∀ (cst cond : val) sa (k : Key) E (P : iProp Σ) (Q : val → iProp Σ) ms mc,
    ⌜k ∈ KVS_keys⌝ -∗
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ dom mc⌝ -∗
    ⌜dom ms = dom mc⌝ -∗
    start_spec -∗
    read_spec -∗
    commit_spec -∗
    (∀ v, {{{ P }}} cond v @[ip_of_address sa]
          {{{ b, RET #b; (⌜b = true⌝ ∗ Q v) ∨ (⌜b = false⌝ ∗ P) }}}) -∗
    (□|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ⌜can_commit m ms mc⌝ ∗
                    ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
                  ▷ ((∃ t, ⌜max_timestamp t m⌝ ∗
                      ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo)) ∨
                    ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ={E, ⊤}=∗ emp)) -∗
    {{{
      P ∗
      ConnectionState cst (Active ms) ∗
      ([∗ map] k ↦ p ∈ mc, k ↦{cst} p.1  ∗ KeyUpdStatus cst k p.2)
    }}}
      wait_on_keyT cst cond #k @[ip_of_address sa]
    {{{ v m, RET #(); Q v ∗
        ⌜dom m = dom ms⌝ ∗
        ConnectionState cst (Active m) ∗
        ([∗ map] k ↦ eo ∈ m, k ↦{cst} (weo_val eo) ∗ KeyUpdStatus cst k false)
    }}}.
  Proof.
    iIntros (cst cond sa k E P Q ms mc k_keys name k_mc ms_mc) "#start #read
       #commit #cond_spec #inv !>%Φ (P & Active & cache) HΦ".
    rewrite/wait_on_keyT.
    wp_pures.
    destruct (proj1 (elem_of_dom mc k) k_mc) as ([v b] & mc_k).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ mc_k with "cache")
          as "((k_v & updated) & cache)".
    clear mc_k.
    wp_apply ("read" with "[//] k_v").
    iIntros "k_v".
    iSpecialize ("cache" with "[$k_v $updated]").
    case: v=>[w|]; last first.
    {
      wp_pures.
      wp_apply (commitT_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & %can_commit & m_kvs & close)".
      iModIntro.
      iExists m, ms, mc.
      iSplitL "Active m_kvs cache".
      { iFrame. by iSplit. }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[$post]") as "_".
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms can_commit.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & %can_commit & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      do 2 (wp_pure _).
      rewrite -ms_mc -m_ms in k_mc.
      rewrite -m_ms.
      wp_apply (simplified_wait_on_keyT_spec with "[//] [//] [//] start read
            commit cond_spec [] [$P $Active $snap]"); last done.
      iModIntro.
      iMod "inv" as "(%m' & %m'_ms & %can_commit' & m'_kvs & close)".
      iModIntro.
      iExists m'.
      iSplit; first done.
      iFrame.
      iIntros "!>snap".
      iMod ("close" with "[$snap]").
      by iModIntro.
    }
    wp_pures.
    wp_apply ("cond_spec" with "P").
    iIntros "% [(-> & Q)|(-> & P)]".
    {
      wp_pures.
      wp_apply (commitT_spec with "[//] commit").
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & %can_commit & m_kvs & close)".
      iModIntro.
      iExists m, ms, mc.
      iSplitL "Active m_kvs cache".
      {
        iFrame.
        by iSplit.
      }
      iIntros "!>(CanStart & post)".
      iMod ("close" with "[$post]") as "_".
      iModIntro.
      wp_pures.
      wp_apply ("start" $! _ _ E with "[//]").
      clear m m_ms can_commit.
      iPoseProof "inv" as "#inv'".
      iMod "inv'" as "(%m & %m_ms & _ & m_kvs & close)".
      iModIntro.
      iExists m.
      iSplitL "CanStart m_kvs"; first iFrame.
      iIntros "!>(Active & m_kvs & snap)".
      iMod ("close" with "[$m_kvs]") as "_".
      iModIntro.
      wp_pures.
      rewrite -ms_mc -m_ms in k_mc.
      rewrite -m_ms.
      by iApply ("HΦ" with "[$Q $Active $snap]").
    }
    wp_pures.
    wp_apply (commitT_spec with "[//] commit").
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & %can_commit & m_kvs & close)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "Active m_kvs cache".
    {
      iFrame.
      by iSplit.
    }
    iIntros "!>(CanStart & post)".
    iMod ("close" with "[$post]") as "_".
    iModIntro.
    wp_pures.
    wp_apply ("start" $! _ _ E with "[//]").
    clear m m_ms can_commit.
    iPoseProof "inv" as "#inv'".
    iMod "inv'" as "(%m & %m_ms & %can_commit & m_kvs & close)".
    iModIntro.
    iExists m.
    iSplitL "CanStart m_kvs"; first iFrame.
    iIntros "!>(Active & m_kvs & snap)".
    iMod ("close" with "[$m_kvs]") as "_".
    iModIntro.
    do 2 (wp_pure _).
    rewrite -ms_mc -m_ms in k_mc.
    rewrite -m_ms.
    wp_apply (simplified_wait_on_keyT_spec with "[//] [//] [//] start read
            commit cond_spec [] [$P $Active $snap]"); last done.
    iModIntro.
    iMod "inv" as "(%m' & %m_m' & _ & snap & close)".
    iModIntro.
    iExists m'.
    iSplit; first done.
    iFrame.
    iIntros "!>snap".
    iMod ("close" with "[$snap]").
    by iModIntro.
  Qed.

End proof.
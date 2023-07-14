From aneris.examples.snapshot_isolation.util Require Import util_code.
From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From iris.algebra Require Import gmap.
From iris.algebra Require Import excl.


Section proof.

Context `{!anerisG Mdl Σ, !User_params, !KVSG Σ, !SI_resources Mdl Σ,
           !SI_client_toolbox}.

  Lemma commitU_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitU c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        ((⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc, 
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, k ↦ₖ h ∗ Seen k h)) >>>.
  Proof.
    iIntros (cst sa E name Φ) "!>HΦ".
    rewrite/commitU.
    wp_pures.
    wp_apply (SI_commit_spec with "[//] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & pre & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [( _ & post)|(_ & post)])"; 
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ";
    iModIntro;
    by wp_pures.
  Qed.

  Lemma commitT_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ⌜can_commit m ms mc⌝ ∗
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitT c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        ([∗ map] k↦ h;p ∈ m; mc, 
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h)) >>>.
  Proof.
    iIntros (cst sa E name Φ) "!>HΦ".
    rewrite/commitT/assert.
    wp_pures.
    wp_apply (SI_commit_spec with "[//] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & (%can_commit & pre) & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [(-> & _ & post)|(_ & %abs & _)])"; try done.
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
    iModIntro.
    by wp_pures.
  Qed.

  Lemma wait_transaction_spec :
    ∀ (c cond : val) (key : Key) (domain: gset Key) sa E 
    (P : iProp Σ) (Q : val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜domain ⊆ KVS_keys⌝ -∗
    ⌜key ∈ domain⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = domain⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
            ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ m v', {{{ P ∗ ConnectionState c (Active m) ∗ ⌜dom m = domain⌝ ∗
              ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) }}}
              cond v' @[ip_of_address sa]
              {{{ m' (b : bool), RET #b;
              ConnectionState c (Active m') ∗ ⌜dom m' = domain⌝ ∗
              ([∗ map] k ↦ h ∈ m', k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
              if b then Q v' else P }}}) -∗
    {{{ P ∗ ConnectionState c CanStart }}}
     wait_transaction c cond #key @[ip_of_address sa]
    {{{ v h, RET #(); ConnectionState c CanStart ∗ Seen key (v :: h) ∗ Q v }}}.
  Proof.
    iIntros (c cond key domain sa E P Q name_sub_E map_sub_keys key_in_map)
    "#shift #cond %Φ !> (HP & CanStart) HΦ".
    rewrite /wait_transaction.
    wp_pures.
    iLöb as "IH".
    wp_apply (SI_start_spec with "[//]").
    iPoseProof "shift" as "shift'".
    iMod "shift'" as "(%m_shift & %m_shift_ & kvs & close)".
    iModIntro.
    iExists m_shift.
    iFrame.
    iIntros "!>(Active & kvs & cache & #seen)".
    iMod ("close" with "kvs") as "_".
    iModIntro.
    wp_pures.
    assert (key ∈ dom m_shift) as key_in_m_shift. { set_solver. }  
    destruct ((proj1 (elem_of_dom m_shift key)) key_in_m_shift) as (h & key_h).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ key_h with "cache") as
        "((key_h & key_upd) & cache)".
    wp_apply (SI_read_spec with "[] key_h"). { set_solver. }
    iIntros "key_h".
    iSpecialize ("cache" with "[$key_h $key_upd]").
    iAssert (∀ m, ⌜dom m = domain⌝  -∗ 
            (∀ v h, ConnectionState c CanStart ∗ Seen key (v :: h) ∗ Q v -∗ Φ #()) -∗ 
            ConnectionState c (Active m) -∗ 
            P -∗
            ([∗ map] k↦y ∈ m, k ↦{ c} hist_val y ∗ KeyUpdStatus c k false) -∗
            WP commitT c ;; 
            (rec: "aux" <> :=
                snapshot_isolation_code.start c ;; 
                match: snapshot_isolation_code.read c #key with
                  InjL <> => commitT c ;; "aux" #()
                | InjR "v" => if: cond "v" then commitT c else commitT c ;; "aux" #()
                end)%V #() @[ip_of_address sa] {{ v, Φ v }})%I as "retry".
    - iIntros (m) "%m_dom HΦ Active HP cache".
      wp_apply (commitT_spec with "[//]").
      iPoseProof "shift" as "shift'".
      iMod "shift'" as "(%m_shift' & %m_shift_dom & mem & close)".
      iModIntro.
      iExists _, _, ((λ h, (hist_val h, false)) <$> m).
      iFrame.
      iSplitL "cache".
      {
        iSplit.
        {
          iPureIntro.
          rewrite bool_decide_spec=>k' k'_key.
          rewrite lookup_fmap.
          by destruct (m !! k').
        }
        iSplit; first by rewrite m_dom.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & mem)".
      iMod ("close" with "[mem]") as "_".
      {
        iPoseProof (big_sepM2_fmap_r _ _ _ m with "mem") as "mem".
        iPoseProof (big_sepM2_sep with "mem") as "(mem & _)".
        iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m_shift' m
                with "[mem] []") as "mem".
        {
          iApply (big_sepM2_impl with "mem").
          iIntros "!>%k' % %h' % %Hh' ?".
          by destruct h'.
        }
        {
          iApply big_sepM2_intro; last done.
          intros k'.
          split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
          set_solver.
        }
        iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
        intros k'.
        split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom; set_solver.
      }
      iModIntro.
      wp_pures.
      iApply ("IH" with "HP CanStart HΦ").
    - destruct h; wp_pures.
      {
        iApply ("retry" with "[//] HΦ Active HP cache").
      }
      wp_apply ("cond" with "[$HP $Active $cache]"); first done.
      iIntros (m_cond []) "(Active & %Heq & cache & HP)"; last first.
      {
        wp_pures.
        iApply ("retry" with "[//] HΦ Active HP cache").
      }
      wp_pures.
      wp_apply (commitT_spec with "[//]").
      iPoseProof "shift" as "shift'".
      iMod "shift'" as "(%m_shift' & %m_shift_dom & mem & close)".
      iModIntro.
      iExists _, _, ((λ h, (hist_val h, false)) <$> m_cond).
      iFrame.
      iSplitL "cache".
      {
        iSplit.
        {
          iPureIntro.
          rewrite bool_decide_spec=>k' k'_key.
          rewrite lookup_fmap.
          by destruct (m_cond !! k').
        }
        iSplit; first by rewrite Heq.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & mem)".
      iMod ("close" with "[mem]") as "_".
      {
        iPoseProof (big_sepM2_fmap_r _ _ _ m_cond with "mem") as "mem".
        iPoseProof (big_sepM2_sep with "mem") as "(mem & _)".
        iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m_shift' m_cond
                with "[mem] []") as "mem".
        {
          iApply (big_sepM2_impl with "mem").
          iIntros "!>%k' % %h' % %Hh' ?".
          by destruct h'.
        }
        {
          iApply big_sepM2_intro; last done.
          intros k'.
          split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
          set_solver.
        }
        iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
        intros k'.
        by split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
        set_solver.
      }
      iModIntro.
      iPoseProof (big_sepM_lookup _ _ _ _ key_h with "seen") as "seen_key".
      iApply ("HΦ" with "[$CanStart $seen_key $HP]").
  Qed.

  Lemma simple_wait_transaction_spec :
    ∀ (c cond v : val) (key : Key) (domain: gset Key) sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜domain ⊆ KVS_keys⌝ -∗
    ⌜key ∈ domain⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = domain⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
            ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}}
            cond v' @[ip_of_address sa]
           {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{ ConnectionState c CanStart }}}
     wait_transaction c cond #key @[ip_of_address sa]
    {{{ h, RET #(); ConnectionState c CanStart ∗ Seen key (v :: h) }}}.
  Proof.
    iIntros (c cond v key map sa E name_sub_E map_sub_keys key_in_map)
    "#shift #cond %Φ !> CanStart HΦ".
    iApply (wait_transaction_spec _ _ _ _ _ _ True (λ v', ⌜v = v'⌝)%I
        with "[//] [//] [//] shift [] [$CanStart] [HΦ]"). 
    - iIntros (m v') "%φ !> (_ & Active & <- & cache) Hφ".
      wp_apply ("cond" with "[//]").
      iIntros (b Heq).
      iApply ("Hφ" with "[$Active $cache]").
      iSplit; first done.
      destruct b; auto. 
    - iIntros (v' h) "!>(CanStart & seen & <-)".
      iApply ("HΦ" with "[$CanStart $seen]").
  Qed.
  
End proof.
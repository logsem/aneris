From aneris.examples.snapshot_isolation.util Require Import util_code.
From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.specs
  Require Import user_params time events aux_defs resource_algebras
  resources specs.
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
    IsConnected c sa -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitU c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc,
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, k ↦ₖ h ∗ Seen k h)) >>>.
  Proof.
    iIntros (cst sa E name) "#HisC %Φ !>HΦ" . 
    rewrite/commitU.
    wp_pures.
    wp_apply (SI_commit_spec with "[//] [$] [HΦ]").
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
    IsConnected c sa -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ⌜can_commit m ms mc⌝ ∗
        ConnectionState c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitT c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ([∗ map] k↦ h;p ∈ m; mc,
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h)) >>>.
  Proof.
    iIntros (cst sa E name) "#HisC %Φ !>HΦ". 
    rewrite/commitT/assert.
    wp_pures.
    wp_apply (SI_commit_spec with "[//] [$] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & (%can_commit & pre) & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [(-> & _ & post)|(_ & %abs & _)])"; try done.
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
    iModIntro.
    by wp_pures.
  Qed.

  Lemma simplified_commitT_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    IsConnected c sa -∗
    <<< ∀∀ (m ms : gmap Key Hist),
        ConnectionState c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ h ∈ ms, k ↦{c} (last h) ∗ KeyUpdStatus c k false) >>>
      commitT c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c sa CanStart ∗
        (** Read-only transaction has been commited.
            We don't need seen predicates as nothing changed. *)
        ([∗ map] k↦ h ∈ m, k ↦ₖ h)>>>.
  Proof.
    iIntros (cst sa E name) "#HisC %Φ !>HΦ" . 
    wp_apply (commitT_spec with "[//][$]").
    iMod "HΦ" as
      "(%m & %ms & (Active & %dom_eq & kvs & cache) & close)".
    iModIntro.
    iExists _, _, ((λ h, (last h, false)) <$> ms).
    iFrame.
    iSplitL "cache".
    {
      iSplit.
      {
        iPureIntro.
        rewrite bool_decide_spec=>k k_key.
        rewrite lookup_fmap.
        destruct (ms !! k) eqn:Hk;
          rewrite Hk; simplify_eq /=; try eauto.
      }
      iSplit; first by rewrite dom_eq.
      iSplit; first by rewrite dom_fmap_L.
      by iApply big_sepM_fmap.
    }
    iIntros "!>(CanStart & kvs)".
    iMod ("close" with "[$CanStart kvs]") as "HΦ"; last done.
    iPoseProof (big_sepM2_fmap_r _ _ _ ms with "kvs") as "kvs".
    iPoseProof (big_sepM2_sep with "kvs") as "(kvs & _)".
    iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m ms
                with "[kvs] []") as "kvs".
    {
      iApply (big_sepM2_impl with "kvs").
      iIntros "!>%k % %h % %Hh ?".
      by destruct (last h).
    }
    {
      iApply big_sepM2_intro; last done.
      intros k.
      split=>/(proj2 (elem_of_dom _ _)) Hk; apply elem_of_dom;
          set_solver.
    }
    iPoseProof (big_sepM2_sepM with "kvs") as "(kvs & _)"; last done.
    intros k.
    split=>/(proj2 (elem_of_dom _ _)) Hk; apply elem_of_dom; set_solver.
  Qed.

  Lemma wait_transaction_spec :
    ∀ (c cond : val) (key : Key) sa E
    (P : iProp Σ) (Q : val → iProp Σ) (Ψ : gmap _ _ → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    IsConnected c sa -∗
      □ (|={⊤, E}=> ∃ m, ⌜key ∈ dom m⌝ ∗ ⌜dom m ⊆ KVS_keys⌝ ∗
              ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ Ψ m ∗
            ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    □ (∀ m, Ψ m ={⊤, E}=∗ ∃ m', ⌜dom m = dom m'⌝ ∗
              ([∗ map] k ↦ h ∈ m', k ↦ₖ h) ∗
            ▷ (([∗ map] k ↦ h ∈ m', k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ m v', {{{ P ∗ Ψ m ∗ ConnectionState c sa (Active m) ∗
              ([∗ map] k ↦ h ∈ m, k ↦{c} (last h) ∗ KeyUpdStatus c k false) }}}
              cond v' @[ip_of_address sa]
              {{{ m' (b : bool), RET #b;
              ConnectionState c sa (Active m') ∗ ⌜dom m' = dom m⌝ ∗ Ψ m' ∗
              ([∗ map] k ↦ h ∈ m', k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗
              if b then Q v' else P }}}) -∗
    {{{ P ∗ ConnectionState c sa CanStart }}}
     wait_transaction c cond #key @[ip_of_address sa]
    {{{ v h, RET #(); ConnectionState c sa CanStart ∗ Seen key (h ++ [v]) ∗ Q v }}}.
  Proof.
    iIntros (c cond key sa E P Q Ψ name_sub_E)
      "#HisC #start #commit #cond".
    iIntros (Φ) "!>(HP & CanStart) HΦ".
    rewrite /wait_transaction.
    wp_pures.
    iLöb as "IH".
    wp_apply (SI_start_spec with "[//][$]").
    iPoseProof "start" as "start'".
    iMod "start'" as "(%m_shift & %key_in_m_shift & %m_sub_keys &
                          kvs & HΨ & close)".
    iModIntro.
    iExists m_shift.
    iFrame.
    iIntros "!>(Active & kvs & cache & #seen)".
    iMod ("close" with "kvs") as "_".
    iModIntro.
    wp_pures.
    destruct ((proj1 (elem_of_dom m_shift key)) key_in_m_shift) as (h & key_h).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ key_h with "cache") as
        "((key_h & key_upd) & cache)".
    wp_apply (SI_read_spec with "[][$][$key_h] "); first set_solver.
    iIntros "key_h".
    iSpecialize ("cache" with "[$key_h $key_upd]").
    destruct (last h) eqn:Hlast; wp_pures.
    wp_apply ("cond" with "[$HP $HΨ $Active $cache //]").
    rename m_shift into m_old.
    iIntros (m_shift []) "(Active & %Heq & HΨ & cache & HP)"; wp_pures.
    all: wp_apply (simplified_commitT_spec with "[//][$]").
    all: iMod ("commit" with "HΨ") as
        "(%m_shift' & %Heq' & kvs & close)".
    all: iModIntro.
    all: iExists _, _.
    all: iFrame.
    all: iSplit; first done.
    all: iIntros "!>(CanStart & kvs)".
    all: iMod ("close" with "kvs") as "_".
    {
      apply last_Some in Hlast as [h0]. simplify_eq /=.
      iApply ("HΦ" with "[$HP $CanStart]").
      iApply (big_sepM_lookup _ _ _ _ key_h with "seen").
    }
    all: iModIntro.
    all: wp_pures.
    all: iApply ("IH" with "HP CanStart HΦ").
  Qed.

  Lemma simple_wait_transaction_spec :
    ∀ (c cond v : val) (key : Key) sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜key ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗  
    □ (|={⊤, E}=> ∃ h, key ↦ₖ h ∗ ▷ (key ↦ₖ h ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}}
            cond v' @[ip_of_address sa]
           {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{ ConnectionState c sa CanStart }}}
     wait_transaction c cond #key @[ip_of_address sa]
    {{{ h, RET #(); ConnectionState c sa CanStart ∗ Seen key (h ++ [v]) }}}.
  Proof.
    iIntros (c cond v key sa E name_sub_E key_keys)
        "#HiC #shift #cond %Φ !> CanStart HΦ".
    iApply (wait_transaction_spec _ _ _ _ _ emp (λ v', ⌜v = v'⌝)%I
      (λ m, ⌜dom m = {[ key ]}⌝)%I
      with "[//] [$] [] [] [] [$CanStart]"); [| | iFrame "#"|];
      last first.
    {
      iIntros "!>%v' %h (CanStart & Seen & <-)".
      iApply ("HΦ" with "[$]").
    }
    { iIntros (m_shift v' Ψ) "!>(_ & %dom_m_shift & Active & cache) HΨ".
      wp_apply ("cond" with "[//]").
      iIntros ([] eq); first rewrite -(eq I).
      all: by iApply ("HΨ" with "[$Active $cache]").
    }
    iIntros "!>%m_shift ->".
    2: iModIntro.
    all: iMod "shift" as "(%h & cache & close)".
    all: iModIntro.
    all: iExists {[ key := h ]}.
    all: iSplit; first (iPureIntro; set_solver).
    2: iSplit; first (iPureIntro; set_solver).
    all: iSplitL "cache"; first iApply (big_sepM_singleton with "cache").
    2: iSplit; first (iPureIntro; set_solver).
    all: iIntros "!>kvs".
    all: iMod ("close" with "[kvs]") as "_"; last done.
    all: by iApply big_sepM_singleton.
  Qed.

End proof.

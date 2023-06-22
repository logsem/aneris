From aneris.examples.snapshot_isolation.util Require Import util_code.
From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From iris.algebra Require Import gmap.


Section proof.
  
Context `{!anerisG Mdl Σ, !User_params, !KVSG Σ, !SI_resources Mdl Σ,
           !SI_specs}.

  Lemma commitU_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    commit_spec -∗
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
    iIntros (cst sa E name) "#commit %Φ !>HΦ".
    rewrite/commitU.
    wp_pures.
    wp_apply ("commit" with "[//] [HΦ]").
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
    commit_spec -∗
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
    iIntros (cst sa E name) "#commit %Φ !>HΦ".
    rewrite/commitT/assert.
    wp_pures.
    wp_apply ("commit" with "[//] [HΦ]").
    iMod "HΦ" as "(%m & %ms & %mc & (%can_commit & pre) & HΦ)".
    iModIntro.
    iExists m, ms, mc.
    iSplitL "pre"; first done.
    iIntros "!>%b (CanStart & [(-> & _ & post)|(_ & %abs & _)])"; try done.
    iMod ("HΦ" with "[$CanStart $post]") as "HΦ".
    iModIntro.
    by wp_pures.
  Qed.

  Lemma simplified_wait_on_keyT_spec :
    ∀ (c cond v : val) (k : Key) ms sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}} cond v' @[ip_of_address sa]
          {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{
      ConnectionState c (Active ms) ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false)
    }}}
      wait_on_keyT c cond k @[ip_of_address sa]
    {{{ m, RET #(); ⌜dom m = dom ms⌝ ∗
      ConnectionState c (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ∃ h, Seen k (v :: h)
    }}}.
  Proof.
  Admitted.

  Lemma wait_on_keyT_spec :
    ∀ (c cond : val) (k : Key) ms sa E
      (P : _ → iProp Σ) (Q : val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ m v, {{{ P m ∗ ConnectionState c (Active m) ∗ ⌜dom m = dom ms⌝ ∗
                ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false)
             }}}
              cond v @[ip_of_address sa]
             {{{ m' (b : bool), RET #b; ConnectionState c (Active m') ∗
                ([∗ map] k ↦ h ∈ m', k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
                if b then Q v else P m'
             }}}) -∗
    {{{
      P ms ∗ ConnectionState c (Active ms) ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false)
    }}}
      wait_on_keyT c cond k @[ip_of_address sa]
    {{{ m v, RET #(); ⌜dom m = dom ms⌝ ∗ Q v ∗
      ConnectionState c (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ∃ h, Seen k (v :: h)
    }}}.
  Proof.
  Admitted.

End proof.
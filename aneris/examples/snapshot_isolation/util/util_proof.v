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

  Lemma wait_on_keyT_spec :
    ∀ (c cond : val) (k : Key) ms sa E
      (P : iProp Σ) (Q : val → iProp Σ) (Φ : _ → iProp Σ),
    (∀ m, Persistent (Φ m)) →
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ Φ m ∗
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ m v, {{{ P ∗ ConnectionState c (Active m) ∗ ⌜dom m = dom ms⌝ ∗
                ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false)
             }}}
              cond v @[ip_of_address sa]
             {{{ m' (b : bool), RET #b; ConnectionState c (Active m') ∗ ⌜dom m' = dom ms⌝ ∗
                ([∗ map] k ↦ h ∈ m', k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
                if b then Q v else P
             }}}) -∗
    {{{
      P ∗ ConnectionState c (Active ms) ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ ms, Seen k h)
    }}}
      wait_on_keyT c cond #k @[ip_of_address sa]
    {{{ m v, RET #(); ⌜dom m = dom ms⌝ ∗ Q v ∗
      ConnectionState c (Active m) ∗ Φ m ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ∃ h, Seen k (v :: h)
    }}}.
  Proof.
    iIntros (c cond k ms sa E P Q Ψ Ψ_pers name ms_keys k_ms) "#inv #cond_spec
         %Φ !> (P & Active & cache & #seen) HΦ".
    rewrite/wait_on_keyT.
    wp_pures.
    iRevert (ms ms_keys k_ms) "inv seen cond_spec HΦ cache Active P".
    iLöb as "IH".
    iIntros (ms ms_keys k_ms) "#inv #seen #cond_spec HΦ cache Active P".
    move: ((proj1 (elem_of_subseteq _ _)) ms_keys _ k_ms)=>k_keys.
    destruct ((proj1 (elem_of_dom ms k)) k_ms) as (h & k_h).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ k_h with "cache") as
        "((k_h & k_upd) & cache)".
    wp_apply (SI_read_spec with "[//] k_h").
    iIntros "k_h".
    iSpecialize ("cache" with "[$k_h $k_upd]").
    move: h k_h=>[|v' h] k_h.
    {
      wp_pures.
      wp_apply (commitT_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iMod "inv'" as "(%m & %m_ms & mem & _ & close)".
      iModIntro.
      iExists m, ms, ((λ h, (hist_val h, false)) <$> ms).
      iFrame.
      iSplitL "cache".
      {
        iSplit.
        { iPureIntro. apply bool_decide_spec=>k' k'_keys. rewrite lookup_fmap.
          by case: (ms !! k'). }
        iSplit; first done.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & data)".
      iPoseProof (big_sepM2_fmap_r _ _ _ ms with "data") as "data".
      iPoseProof (big_sepM2_sep with "data") as "(mem & _)".
      iMod ("close" with "[mem]") as "_".
      {
        iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m ms
                with "[mem] []") as "mem".
        {
          iApply (big_sepM2_impl with "mem").
          iIntros "!>%k' %h %h' % %Hh' k'_h"=>{Hh'}.
          by case: h'.
        }
        {
          iApply big_sepM2_intro; last done.
          move=>k'.
          split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                                rewrite ?m_ms // -?m_ms//.
        }
        iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
        move=>k'.
        split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                                rewrite ?m_ms // -?m_ms//.
      }
      iModIntro.
      wp_pures.
      wp_apply (SI_start_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iMod "inv'" as "(%m' & %m'_ms & mem & _ & close)".
      iModIntro.
      iExists m'.
      iFrame.
      iIntros "!>(Active & mem & cache & #seen')".
      iMod ("close" with "mem") as "_".
      iModIntro.
      wp_pures.
      rewrite -m'_ms in ms_keys k_ms.
      rewrite -m'_ms.
      wp_apply ("IH" with "[//] [//] inv seen' cond_spec HΦ cache Active P").
    }
    wp_pures.
    wp_apply ("cond_spec" with "[$P $Active $cache]"); first done.
    iIntros (ms' b).
    case: b; last first.
    {
      iIntros "(Active & %ms'_ms & cache & P)".
      wp_pures.
      wp_apply (commitT_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iMod "inv'" as "(%m & %m_ms & mem & _ & close)".
      iModIntro.
      iExists m, ms', ((λ h, (hist_val h, false)) <$> ms').
      iFrame.
      iSplitL "cache".
      {
        iSplit.
        { iPureIntro. apply bool_decide_spec=>k' k'_keys. rewrite lookup_fmap.
          by case: (ms' !! k'). }
        iSplit; first by rewrite m_ms.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & data)".
      iPoseProof (big_sepM2_fmap_r _ _ _ ms' with "data") as "data".
      iPoseProof (big_sepM2_sep with "data") as "(mem & _)".
      iMod ("close" with "[mem]") as "_".
      {
        iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m ms'
                with "[mem] []") as "mem".
        {
          iApply (big_sepM2_impl with "mem").
          iIntros "!>%k' %h' %h'' % %Hh'' k'_h'"=>{Hh''}.
          by case: h''.
        }
        {
          iApply big_sepM2_intro; last done.
          move=>k'.
          split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                      rewrite ?ms'_ms -?m_ms // ?m_ms -?ms'_ms//.
        }
        iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
        move=>k'.
        split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                      rewrite ?ms'_ms -?m_ms // ?m_ms -?ms'_ms//.
      }
      iModIntro.
      wp_pures.
      wp_apply (SI_start_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iClear (m m_ms) "".
      iMod "inv'" as "(%m & %m_ms & mem & _ & close)".
      iModIntro.
      iExists m.
      iFrame.
      iIntros "!>(Active & mem & cache & #seen')".
      iMod ("close" with "mem") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms in ms_keys k_ms.
      rewrite -m_ms.
      wp_apply ("IH" with "[//] [//] inv seen' cond_spec HΦ cache Active P").
    }
    iIntros "(Active & %ms'_ms & cache & Q)".
    wp_pures.
    wp_apply (commitT_spec with "[//]").
    iPoseProof "inv" as "inv'".
    iMod "inv'" as "(%m & %m_ms & mem & _ & close)".
    iModIntro.
    iExists m, ms', ((λ h, (hist_val h, false)) <$> ms').
    iFrame.
    iSplitL "cache".
    {
      iSplit.
      { iPureIntro. apply bool_decide_spec=>k' k'_keys. rewrite lookup_fmap.
        by case: (ms' !! k'). }
      iSplit; first by rewrite ms'_ms.
      iSplit; first by rewrite dom_fmap_L.
      by iApply big_sepM_fmap.
    }
    iIntros "!>(CanStart & data)".
    iPoseProof (big_sepM2_fmap_r _ _ _ ms' with "data") as "data".
    iPoseProof (big_sepM2_sep with "data") as "(mem & _)".
    iMod ("close" with "[mem]") as "_".
    {
      iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m ms'
              with "[mem] []") as "mem".
      {
        iApply (big_sepM2_impl with "mem").
        iIntros "!>%k' %h' %h'' % %Hh'' k'_h'"=>{Hh''}.
        by case: h''.
      }
      {
        iApply big_sepM2_intro; last done.
        move=>k'.
        split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                      rewrite ?ms'_ms -?m_ms // ?m_ms -?ms'_ms//.
      }
      iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
      move=>k'.
      split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
                                      rewrite ?ms'_ms -?m_ms // ?m_ms -?ms'_ms//.
    }
    iModIntro.
    wp_pures.
    wp_apply (SI_start_spec with "[//]").
    iPoseProof "inv" as "inv'".
    iMod "inv'" as "(%m' & %m'_ms & mem & #HΨ & close)".
    iModIntro.
    iExists m'.
    iFrame.
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "mem") as "_".
    iModIntro.
    wp_pures.
    iApply ("HΦ" with "[$Active $cache $Q]").
    do 2 (iSplit; first done).
    iExists h.
    by iPoseProof (big_sepM_lookup with "seen") as "seen_k".
  Qed.

  Lemma simplified_wait_on_keyT_spec :
    ∀ (c cond v : val) (k : Key) ms sa E Φ,
    (∀ m, Persistent (Φ m)) →
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ Φ m ∗
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}} cond v' @[ip_of_address sa]
          {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{
      ConnectionState c (Active ms) ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ ms, Seen k h)
    }}}
      wait_on_keyT c cond #k @[ip_of_address sa]
    {{{ m, RET #(); ⌜dom m = dom ms⌝ ∗ Φ m ∗
      ConnectionState c (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ∃ h, Seen k (v :: h)
    }}}.
  Proof.
    iIntros (c cond v k ms sa E Ψ Ψ_pers name ms_keys k_ms) "#inv #cond_spec %Φ !> 
        (Active & cache & #seen) HΦ".
    wp_apply (wait_on_keyT_spec _ _ _ _ _ _ emp (λ v', ⌜v = v'⌝)%I
          with "[//] [//] [//] inv [] [$Active $cache $seen] [HΦ]").
    {
      iIntros (m v' ψ) "!>(_ & Active & %m_ms & cache) Hψ".
      wp_apply ("cond_spec" with "[//]").
      iIntros ([] v_v'); iApply ("Hψ" with "[$Active $cache]"); iFrame "%".
      by rewrite v_v'.
    }
    iIntros "!>%m %v' (%m_ms & <- & Active & HΨ & cache & (%h & #seen_k))".
    iApply ("HΦ" with "[$Active $cache $HΨ]").
    iFrame "%".
    by iExists h.
  Qed.

End proof.
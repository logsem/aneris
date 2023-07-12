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

  Lemma wait_on_keyT_spec :
    ∀ (c cond : val) (k : Key) ms sa E (P P_tok : iProp Σ)
      (Q : val → iProp Σ) (Q_tok φ : _ → _ → _ → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (∀ v h, P_tok ∗ Q v ∗ Seen k (v :: h) ={⊤, E}=∗
          ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ φ m v h ∗ Q_tok m v h ∗
            ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ Q_tok m v h ={E, ⊤}=∗ emp)) -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗
          ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
            ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ m v', {{{ P ∗ ConnectionState c (Active m) ∗ ⌜dom m = dom ms⌝ ∗
              ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false)
            }}}
            cond v' @[ip_of_address sa]
            {{{ m' (b : bool), RET #b;
              ConnectionState c (Active m') ∗ ⌜dom m' = dom ms⌝ ∗
              ([∗ map] k ↦ h ∈ m', k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
              if b then Q v' else P
            }}}) -∗
    {{{
      P ∗ P_tok ∗ ConnectionState c (Active ms) ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ ms, Seen k h)
    }}}
     wait_on_keyT c cond #k @[ip_of_address sa]
    {{{ m v h, RET #(); ⌜dom m = dom ms⌝ ∗ φ m v h ∗
      ConnectionState c (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ m, Seen k h)
    }}}.
  Proof.
    iIntros (c cond k ms sa E P P_tok Q Q_tok) "%φ %name %ms_keys %k_ms #finish
      #inv #cond_spec %Φ !> (P & P_tok & Active & cache & Seen) HΦ".
    rewrite/wait_on_keyT.
    wp_pures.
    iRevert (ms ms_keys k_ms) "inv finish cond_spec HΦ cache Active P Seen".
    iLöb as "IH".
    iIntros (ms ms_keys k_ms) "#inv #finish #cond_spec HΦ cache Active P #Seen".
    move: ((proj1 (elem_of_subseteq _ _)) ms_keys _ k_ms)=>k_keys.
    destruct ((proj1 (elem_of_dom ms k)) k_ms) as (h & k_h).
    iPoseProof (big_sepM_lookup_acc _ _ _ _ k_h with "cache") as
        "((k_h & k_upd) & cache)".
    wp_apply (SI_read_spec with "[//] k_h").
    iIntros "k_h".
    iSpecialize ("cache" with "[$k_h $k_upd]").
    iAssert (∀ ms', ⌜dom ms = dom ms'⌝ -∗ P_tok -∗ (∀ m v0 h0,
         ⌜dom m = dom ms⌝ ∗ φ m v0 h0 ∗ ConnectionState c (Active m) ∗
         ([∗ map] k0↦h1 ∈ m, k0 ↦{ c} hist_val h1 ∗
          KeyUpdStatus c k0 false) ∗ ([∗ map] k0↦h1 ∈ m, Seen k0 h1) -∗
         Φ #()) -∗ ConnectionState c (Active ms') -∗ P -∗
          ([∗ map] k0↦y ∈ ms', k0 ↦{ c} hist_val y ∗ KeyUpdStatus c k0 false) -∗
       WP commitT c ;; 
       snapshot_isolation_code.start c ;; 
       (rec: "aux" <> :=
          match: snapshot_isolation_code.read c #k with
            InjL <> =>
              commitT c ;; snapshot_isolation_code.start c ;; "aux" #()
          | InjR "v" =>
            if: cond "v" then commitT c ;; snapshot_isolation_code.start c
            else commitT c ;; snapshot_isolation_code.start c ;; "aux" #()
          end)%V #() @[ip_of_address sa] {{ v, Φ v }})%I as "retry".
    {
      iClear "Seen".
      iIntros (ms') "%ms_ms' P_tok HΦ Active P cache".
      wp_apply (commitT_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iMod "inv'" as "(%m & %m_ms & mem & close)".
      iModIntro.
      iExists _, _, ((λ h, (hist_val h, false)) <$> ms').
      iFrame.
      iSplitL "cache".
      {
        iSplit.
        {
          iPureIntro.
          rewrite bool_decide_spec=>k' k'_key.
          rewrite lookup_fmap.
          by case: (ms' !! k').
        }
        iSplit; first by rewrite m_ms.
        iSplit; first by rewrite dom_fmap_L.
        by iApply big_sepM_fmap.
      }
      iIntros "!>(CanStart & mem)".
      iMod ("close" with "[mem]") as "_".
      {
        iPoseProof (big_sepM2_fmap_r _ _ _ ms' with "mem") as "mem".
        iPoseProof (big_sepM2_sep with "mem") as "(mem & _)".
        iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m ms'
                with "[mem] []") as "mem".
        {
          iApply (big_sepM2_impl with "mem").
          iIntros "!>%k' % %h' % %Hh' ?"=>{Hh'}.
          by case: h'.
        }
        {
          iApply big_sepM2_intro; last done.
          move=>k'.
          by split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
            [rewrite -ms_ms' -m_ms|rewrite m_ms ms_ms'].
        }
        iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
        move=>k'.
        by split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
            [rewrite -ms_ms' -m_ms|rewrite m_ms ms_ms'].
      }
      iModIntro.
      wp_pures.
      wp_apply (SI_start_spec with "[//]").
      iPoseProof "inv" as "inv'".
      iClear (m m_ms) "".
      iMod "inv'" as "(%m & %m_ms & mem & close)".
      iModIntro.
      iExists m.
      iFrame.
      iIntros "!>(Active & mem & cache & #Seen)".
      iMod ("close" with "mem") as "_".
      iModIntro.
      wp_pures.
      rewrite -m_ms.
      by iApply ("IH" with
          "P_tok [] [] inv finish cond_spec HΦ cache Active P Seen");
        rewrite m_ms.
    }
    move: h k_h=>[|v' h] k_h. 
    { wp_pures. iApply ("retry" with "[//] P_tok HΦ Active P cache"). }
    wp_pures.
    wp_apply ("cond_spec" with "[$P $Active $cache]"); first done.
    iIntros (m []) "(Active & %m_ms & cache & result)"; last first.
    {
      wp_pures.
      rewrite -m_ms.
      by iApply ("retry" with "[] P_tok HΦ Active result cache").
    }
    iClear "IH retry cond_spec".
    wp_pures.
    wp_apply (commitT_spec with "[//]").
    iPoseProof (big_sepM_lookup _ _ _ _ k_h with "Seen") as "#Seen_k".
    iPoseProof "inv" as "inv'".
    iMod "inv'" as "(%m' & %m'_ms & mem & close)".
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
        by case: (m !! k').
      }
      iSplit; first by rewrite m_ms.
      iSplit; first by rewrite dom_fmap_L.
      by iApply big_sepM_fmap.
    }
    iIntros "!>(CanStart & mem)".
    iMod ("close" with "[mem]") as "_".
    {
      iPoseProof (big_sepM2_fmap_r _ _ _ m with "mem") as "mem".
      iPoseProof (big_sepM2_sep with "mem") as "(mem & _)".
      iPoseProof (big_sepM2_sep_2 (λ k h _, k ↦ₖ h)%I (λ _ _ _, emp)%I m' m
              with "[mem] []") as "mem".
      {
        iApply (big_sepM2_impl with "mem").
        iIntros "!>%k' % %h' % %Hh' ?"=>{Hh'}.
        by case: h'.
      }
      {
        iApply big_sepM2_intro; last done.
        move=>k'.
        by split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
          [rewrite m_ms -m'_ms|rewrite m'_ms -m_ms].
      }
      iPoseProof (big_sepM2_sepM with "mem") as "(mem & _)"; last done.
      move=>k'.
      by split=>/(proj2 (elem_of_dom _ _)) Hk'; apply elem_of_dom;
          [rewrite m_ms -m'_ms|rewrite m'_ms -m_ms].
    }
    iModIntro.
    wp_pures.
    iClear (m m_ms m' m'_ms) "".
    wp_apply (SI_start_spec with "[//]").
    iMod ("finish" with "[$P_tok $result $Seen_k]") as "(%m & %m_ms &
        mem & φ & Q_tok & close)".
    iModIntro.
    iExists m.
    iFrame.
    iIntros "!>(Active & mem & cache & #Seen')".
    iMod ("close" with "[$mem $Q_tok]") as "_".
    iApply "HΦ".
    by iFrame "∗#%".
  Qed.

  Lemma simplified_wait_on_keyT_spec :
    ∀ (c cond v : val) (k : Key) ms sa E φ P_tok Q_tok,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜dom ms ⊆ KVS_keys⌝ -∗
    ⌜k ∈ dom ms⌝ -∗
    □ (∀ h, Seen k (v :: h) ∗ P_tok ={⊤, E}=∗ ∃ m, ⌜dom m = dom ms⌝ ∗
          ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ φ m ∗ Q_tok ∗ 
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗ Q_tok ={E, ⊤}=∗ emp)) -∗
    □ (|={⊤, E}=> ∃ m, ⌜dom m = dom ms⌝ ∗ ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
              ▷ (([∗ map] k ↦ h ∈ m, k ↦ₖ h) ={E, ⊤}=∗ emp)) -∗
    (∀ v', {{{ True }}} cond v' @[ip_of_address sa]
          {{{ (b : bool), RET #b; ⌜b → v = v'⌝ }}}) -∗
    {{{
      ConnectionState c (Active ms) ∗ P_tok ∗
      ([∗ map] k ↦ h ∈ ms, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ ms, Seen k h)
    }}}
      wait_on_keyT c cond #k @[ip_of_address sa]
    {{{ m, RET #(); ⌜dom m = dom ms⌝ ∗ φ m ∗
      ConnectionState c (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ m, Seen k h)
    }}}.
  Proof.
    iIntros (cst cond v k ms sa E φ P_tok Q_tok name ms_keys k_ms)
      "#finish #inv #cond_spec %Φ !> (Active & P_tok & cache & #Seen) HΦ".
    iApply (wait_on_keyT_spec _ _ _ _ _ _ True P_tok (λ v', ⌜v = v'⌝)%I
          (λ _ _ _, Q_tok) (λ m _ _, φ m) with "[//] [//] [//] [] inv []
          [$P_tok $Active $cache $Seen] [HΦ]").
    {
      iIntros "!>% %h (P_tok & <- & #Seen')".
      iApply ("finish" with "[$]").
    }
    {
      iIntros (m v' Ψ) "!>(_ & Active & %m_ms & cache) HΨ".
      wp_apply ("cond_spec" with "[//]").
      iIntros (b v_v').
      iApply ("HΨ" with "[$Active $cache]").
      iSplit; first done.
      by move: b v_v'=> [/(_ I)<-|].
    }
    iIntros "!>% % %".
    iApply "HΦ".
  Qed.

End proof.
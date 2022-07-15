From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting adequacy.
From aneris.aneris_lang.lib Require Import par_proof.
From aneris.examples.dscm.spec Require Import base time events resources init stdpp_utils utils.
From aneris.examples.dscm.clients Require Import example2_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof.

Section with_Σ.
  Context `{!anerisG Mdl Σ, !spawnG Σ}.
  Context  (dbs : list socket_address) (Hdbs : NoDup dbs) (keys : gset Key).

  Program Instance myparams : DB_params :=
    {| DB_addresses := dbs;
       DB_keys := keys;
       DB_addresses_NoDup := Hdbs;
       DB_InvName := nroot .@ "dbinv";
       DB_serialization := int_serialization;
    |}.

  Context `{!DB_time, !DB_events, !Maximals_Computing, !DB_resources Mdl Σ}.

  Definition N := nroot.@"inv".

  Definition thread_inv (k : Key) (sa1 sa2 : socket_address)
             (n1 n2 : Z) : iProp Σ :=
    k ↦ₖ None ∨
    ∃ we, k ↦ₖ Some (mval_of_we we) ∗
          (⌜mval_of_we we = (#n1, WE_timed we, sa1)⌝ ∨
           ⌜mval_of_we we = (#n2, WE_timed we, sa2)⌝).

  Lemma thread_inv_sym k sa1 sa2 n1 n2 :
    ⊢ thread_inv k sa1 sa2 n1 n2 ↔ thread_inv k sa2 sa1 n2 n1.
  Proof.
    iSplit;
      iDestruct 1 as "[$ | Hinv]"; iRight;
      iDestruct "Hinv" as (we) "[Hk [Hinv | Hinv]]";
      iExists we; by iFrame.
  Qed.

  Lemma thread_write_spec (wr : val) sa1 sa2 (k : Key) (n1 n2 : Z) :
    k ∈ DB_keys →
    write_spec wr sa1 -∗
    inv N (thread_inv k sa1 sa2 n1 n2) -∗
    Obs [] -∗                   (* Is this needed? *)
    Writes sa1 [] -∗
    WP wr #k #n1 @[ip_of_address sa1]
       {{ v, ⌜v = #()⌝ ∗
              ∃ we1 h h1f,
              ⌜mval_of_we we1 = (#n1, WE_timed we1, sa1)⌝ ∗
              ⌜WE_key we1 = k⌝ ∗
              ⌜hist_at_key k h1f = []⌝ ∗
              Obs (h ++ h1f ++ [we1]) ∗
              Writes sa1 [we1] ∗
              (⌜h = []⌝ ∨
               (∃ we2 h2f, ⌜h = h2f ++ [we2]⌝ ∗
                           ⌜mval_of_we we2 = (#n2, WE_timed we2, sa2)⌝ ∗
                           ⌜hist_at_origin sa1 h2f = []⌝)) }}.
  Proof.
    iIntros (Hk) "#Hwr #Hinv Hobs Hwrites".
    wp_pures.
    iDestruct (write_spec_write_spec_atomic with "Hwr") as "Hwr'".
    iApply ("Hwr'" $! (⊤ ∖ ↑N) k (SerVal #n1) with "[] []");
      [ solve_ndisj | done |].
    iInv N as ">HI" "Hclose".
    iDestruct "HI" as "[Hk | HI]".
    { iModIntro.
      iExists [], [], None.
      iFrame "Hobs Hwrites Hk".
      iSplit; [done|].
      iIntros "!>" (hf a_new) "H".
      iDestruct "H" as (Hatkey Hkey Hval Horig Hle) "(Hk & Hobs & Hwrites)".
      iMod ("Hclose" with "[Hk]") as "_".
      { iRight. iExists a_new.
        iFrame. iLeft. rewrite /mval_of_we.
        rewrite Hval. iNext. iPureIntro.
        by f_equiv. }
      iModIntro.
      iSplit; [done|].
      iExists a_new, [], hf.
      iSplit.
      { simplify_eq. rewrite /mval_of_we. iPureIntro. by do 2 f_equiv. }
      iSplit; [done|].
      iSplit; [ by iPureIntro; apply last_None | ].
      iFrame "Hobs Hwrites".
      by iLeft. }
    iDestruct "HI" as (we) "[Hk Hkval]".
    iDestruct "Hkval" as %[Hkval | Hkval].
    { (* Solve contradiction *)
      iMod (OwnMemKey_key with "Hk") as "[Hk %Hkey]"; [solve_ndisj|].
      iMod (OwnMemKey_origin_in_Writes with "Hk Hwrites")
        as "(Hk & Hwrites & %Hin)";
        [ solve_ndisj | done | by inversion Hkval |].
      set_solver. }
    iMod (OwnMemKey_some_obs with "Hk") as "[Hk Hobs']"; [ solve_ndisj | ].
    iDestruct "Hobs'" as (h1 e) "(#Hobs' & %Hatkey' & %Hmval)".
    pose proof (at_key_hist_at_key_inv _ _ _ Hatkey') as
        (h2f1 & h2f2 & [-> Hnin]).
    iMod (Obs_get_smaller h2f1 with "Hobs'") as "Hobs''".
    { solve_ndisj. }
    { rewrite -{1}(right_id _ app h2f1).
      apply prefix_app, prefix_nil. }
    iMod (Writes_obs_at_origin with "[$Hwrites $Hobs'']")
      as "[Hwrites %Horig_le]".
    iModIntro.
    iExists (h2f1 ++ [e] ++ h2f2), [], (Some e).
    rewrite -Hmval.
    iFrame "Hwrites Hobs' Hk".
    iSplit; [ done |].
    iIntros "!>" (hf a_new) "H".
    iDestruct "H" as (Hatkey Hkey Hval Horig Hle) "(Hk & Hobs''' & Hwrites)".
    iMod ("Hclose" with "[Hk]") as "_".
    { iRight. iNext.
      iExists a_new.
      iFrame. iLeft.
      iPureIntro.
      inversion Hval.
      simplify_eq. rewrite /mval_of_we. f_equiv. }
    iModIntro.
    iSplit; [done|].
    replace ((h2f1 ++ [e] ++ h2f2) ++ hf ++ [a_new]) with
        ((h2f1 ++ [e]) ++ (h2f2 ++ hf) ++ [a_new]) by by rewrite !assoc.
    iExists a_new, _, (h2f2 ++ hf).
    inversion Hval.
    rewrite /mval_of_we.
    iFrame.
    iSplit; [ iPureIntro; by f_equiv | ].
    iSplit; [done|].
    iSplit.
    { iPureIntro. rewrite hist_at_key_frame_l_prefix; by apply last_None. }
    iRight.
    iExists e, h2f1.
    iSplit; [done|].
    iSplit.
    { iPureIntro.
      inversion Hmval.
      inversion Hkval.
      f_equiv; [by f_equiv|done]. }
    iPureIntro.
    inversion Horig_le as [h' Horig_le'].
    setoid_rewrite (comm eq) in Horig_le'.
    apply app_nil in Horig_le'.
    by destruct Horig_le' as [Horig_le' _].
  Qed.

  Lemma thread_read_spec (rd : val) sa1 sa2 (k : Key) (n1 n2 : Z) we1 h h1f :
    k ∈ DB_keys →
    sa1 ≠ sa2 →
    WE_key we1 = k →
    mval_of_we we1 = (#n1, WE_timed we1, sa1) →
    hist_at_key k h1f = [] →
    GlobalInv -∗
    read_spec rd sa1 -∗
    inv N (thread_inv k sa1 sa2 n1 n2) -∗
    Obs (h ++ h1f ++ [we1]) -∗
    Writes sa1 [we1] -∗
    WP rd #k @[ip_of_address sa1]
       {{ v, ∃ h',
            Obs (h ++ h1f ++ [we1] ++ h') ∗
            Writes sa1 [we1] ∗
            ((⌜v = InjRV #n1⌝ ∗ ⌜h' = []⌝) ∨
             (⌜v = InjRV #n2⌝ ∗
              (∃ we2' h2f', ⌜h' = h2f' ++ [we2']⌝ ∗
                            ⌜mval_of_we we2' = (#n2, WE_timed we2', sa2)⌝ ∗
                            ⌜hist_at_origin sa1 h2f' = []⌝))) }}.
  Proof.
    iIntros (Hk Hsaneq Hkey Hmval Hatkey) "#HGinv #Hrd #Hinv #Hobs Hwrites".
    iDestruct (read_spec_read_spec_atomic with "Hrd") as "Hrd'".
    iApply ("Hrd'" $! (⊤ ∖ ↑N) k with "[] []");
      [ solve_ndisj | done |].
    iInv N as ">HI" "Hclose".
    iDestruct "HI" as "[Hk | HI]".
    { iMod (OwnMemKey_none_obs with "[$Hk $Hobs]") as "[Hk %Hatkey']";
        [solve_ndisj|].
      rewrite /hist_at_key !filter_app filter_cons_True in Hatkey'; [|done].
      assert ([] ≠ filter (λ x : we, WE_key x = k) h ++
            filter (λ x : we, WE_key x = k) h1f ++ [we1]).
      { rewrite assoc. apply app_cons_not_nil. }
      done. }
    iDestruct "HI" as (we) "[Hk [%HI | %HI]]".
    {
      iMod (OwnMemKey_key with "Hk") as "[Hk %Hkkey]"; [solve_ndisj|].
      iMod (OwnMemKey_origin_in_Writes with "Hk Hwrites")
        as "(Hk & Hwrites & %Hin)"; [solve_ndisj|done|by inversion HI|].
      iModIntro.
      iExists _, _, (Some we).
      iFrame "Hobs Hk".
      assert (we = we1) as -> by set_solver.
      iSplit; [eauto|].
      { iPureIntro. rewrite assoc. by apply at_key_snoc_some. }
      iIntros "!> [[%Hcont _] | H]"; [done|].
      iDestruct "H" as (we Hweeq) "Hk".
      inversion Hweeq as [Heq]. rewrite -Heq.
      iMod ("Hclose" with "[Hk]") as "_".
      { iRight. iNext. iExists we1. iFrame "Hk".
        iLeft. iPureIntro. apply HI. }
      iModIntro.
      iExists [].
      iFrame "Hobs Hwrites".
      inversion HI as ([Hweval Hweorig]).
      iLeft. done.
    }
    iMod (OwnMemKey_key with "Hk") as "[Hk %Hkkey]"; [solve_ndisj|].
    rewrite assoc.
    iMod (OwnMemKey_Obs_extend with "HGinv Hobs Hk") as "[Hk [%h2f #Hobs']]";
      [ solve_ndisj | by simplify_eq | by inversion Hmval;
                                       inversion HI; naive_solver |].
    iModIntro.
    iExists _, _, (Some we).
    iFrame "Hobs' Hk".
    iSplit; [eauto|].
    { iPureIntro. rewrite !assoc. by apply at_key_snoc_some. }
    iIntros "!> [[%Hcont _] | H]"; [done|].
    iDestruct "H" as (we' Hweeq) "Hk".
    inversion Hweeq as [Heq]. rewrite -Heq.
    iMod ("Hclose" with "[Hk]") as "_".
    { iRight. iNext. iExists we. iFrame "Hk".
      iRight. iPureIntro. apply HI. }
    replace (h ++ h1f ++ [we1] ++ h2f ++ [we]) with
         ((h ++ h1f) ++ [we1] ++ (h2f ++ [we])); last first.
    { rewrite !assoc. done. }
    iMod (Writes_Obs_origin_frame _ [] with "Hwrites Hobs'")
      as "[Hwrites %Horig]";
      [solve_ndisj|].
    iModIntro.
    iExists _.
    rewrite -!assoc.
    iFrame "Hobs' Hwrites".
    inversion HI as ([Hweval Hweorig]).
    iRight. iSplit; [done|].
    iExists we, h2f. iSplit; [done|].
    iSplit; [done|].
    iPureIntro.
    rewrite /hist_at_origin in Horig.
    rewrite filter_app in Horig.
    apply app_eq_nil in Horig.
    naive_solver.
  Qed.

  Lemma thread_spec sa1 sa2 (k : Key) (n1 n2 : Z) init dbsv :
    is_list DB_addresses dbsv →
    sa1 ∉ DB_addresses →
    k ∈ DB_keys →
    sa1 ≠ sa2 →
    GlobalInv -∗
    inv N (thread_inv k sa1 sa2 n1 n2) -∗
    unfixed {[sa1]} -∗
    ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ DB_socket_proto) -∗
    sa1 ⤳ (∅, ∅) -∗
    free_ports (ip_of_address sa1) {[port_of_address sa1]} -∗
    init_spec init -∗
    WP thread init sa1 k n1 dbsv @[ip_of_address sa1]
       {{ v, ∃ h2f1 h1f we1 h2f2,
            Obs (h2f1 ++ h1f ++ [we1] ++ h2f2) ∗
            Writes sa1 [we1] ∗
            ⌜mval_of_we we1 = (#n1, WE_timed we1, sa1)⌝ ∗
            ⌜WE_key we1 = k⌝ ∗
            ⌜hist_at_key k h1f = []⌝ ∗
            (⌜h2f1 = []⌝ ∨
             (∃ we2 h2f1', ⌜h2f1 = h2f1' ++ [we2]⌝ ∗
                           ⌜mval_of_we we2 =
                           (#n2, WE_timed we2, sa2)⌝ ∗
                           ⌜hist_at_origin sa1 h2f1' = []⌝)) ∗
            ((⌜v = InjRV #n1⌝ ∗ ⌜h2f2 = []⌝) ∨
             (⌜v = InjRV #n2⌝ ∗
              (∃ we2' h2f2', ⌜h2f2 = h2f2' ++ [we2']⌝ ∗
                             ⌜mval_of_we we2' = (#n2, WE_timed we2', sa2)⌝ ∗
                             ⌜hist_at_origin sa1 h2f2' = []⌝))) }}.
  Proof.
    iIntros (Hdbsv HsaninA Hk Hsaneq)
            "#HGinv #Hinv Hunfixed Hlist Hsa1 Hfree Hinit".
    wp_pures. wp_lam.
    wp_smart_apply ("Hinit" with "[//] [//] [-]"); [by iFrame|].
    iIntros (rd wr) "(Hobs & Hwrites & Hrd & Hwr)".
    wp_pures.
    iDestruct (thread_write_spec with "Hwr Hinv Hobs Hwrites") as "Hwr'"; [done|].
    wp_smart_apply (aneris_wp_wand with "Hwr'").
    iIntros (v) "[_ H]".
    iDestruct "H" as (we1 h2f1 h1f Hmval Hkey Hhist) "(Hobs & Hwrites & %Hh2f1)".
    iDestruct (thread_read_spec with "HGinv Hrd Hinv Hobs Hwrites") as "Hrd'";
      [done..|].
    wp_smart_apply (aneris_wp_wand with "Hrd'").
    iIntros (w) "H".
    iDestruct "H" as (h2f2) "(Hobs & Hwrites & %Hh2f2)".
    iExists h2f1, h1f, we1, h2f2.
    iFrame. done.
  Qed.

  Lemma prog_spec ip sa1 sa2 init k (n1 n2 : Z) dbsv :
    is_list DB_addresses dbsv →
    k ∈ DB_keys →
    ip_of_address sa1 = ip →
    ip_of_address sa2 = ip →
    sa1 ∉ DB_addresses →
    sa2 ∉ DB_addresses →
    sa1 ≠ sa2 →
    GlobalInv -∗
    init_spec init -∗
    {{{ sa1 ⤳ (∅, ∅) ∗ sa2 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa1) {[port_of_address sa1]} ∗
        free_ports (ip_of_address sa2) {[port_of_address sa2]} ∗
        k ↦ₖ None ∗ unfixed {[sa1;sa2]} ∗
        ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ DB_socket_proto) }}}
      prog init sa1 sa2 k n1 n2 dbsv @[ip]
    {{{ (v : val), RET v; ⌜v = (SOMEV #n1, SOMEV #n1)%V⌝ ∨
                          ⌜v = (SOMEV #n1, SOMEV #n2)%V⌝ ∨
                          ⌜v = (SOMEV #n2, SOMEV #n2)%V⌝}}}.
  Proof.
    iIntros (Hlist Hkin Hip1 Hip2 Hsanin1 Hsanin2 Hsaneq).
    iIntros "#HGInv #Hinit !>" (Φ) "(Hsa1 & Hsa2 & Hsap1 & Hsap2 & Hk & Hunfixed & #Hlist) HΦ".
    rewrite /prog.
    iMod (inv_alloc N _ (thread_inv k sa1 sa2 n1 n2) with "[Hk]") as "#Hinv1";
      [by iFrame|].
    iDestruct (inv_iff with "Hinv1 []") as "Hinv2".
    { iIntros "!> !>". iApply thread_inv_sym. }
    do 2 wp_pure _.
    iApply aneris_wp_fupd.
    iDestruct (unfixed_split with "Hunfixed") as "[Hunfixed1 Hunfixed2]";
      [set_solver|].
    wp_smart_apply (wp_par with "[Hsa1 Hsap1 Hunfixed1] [Hsa2 Hsap2 Hunfixed2]").
    { rewrite -Hip1. by iApply (thread_spec sa1 sa2 k n1 n2 init dbsv
                                  with "[$] [$] [$] [$] [$] [$]"). }
    { rewrite -Hip2. by iApply (thread_spec sa2 sa1 k n2 n1 init dbsv
                                  with "[$] [$] [$] [$] [$] [$]"). }
    iIntros (v1 v2) "[H1 H2]".
    iIntros "!>".
    iClear "Hinit Hlist Hinv1 Hinv2".
    iDestruct "H1" as (sa1h2f1 sa1h1f sa1we1 sa1h2f2)
      "(H1Obs & H1Writes & %H1mval & %H1k & %H1atkey & %H1h1 & %H1h2)".
    iDestruct "H2" as (sa2h2f1 sa2h1f sa2we1 sa2h2f2)
      "(H2Obs & H2Writes & %H2mval & %H2k & %H2atkey & %H2h1 & %H2h2)".
    (** Resolve all the succeeding cases *)
    destruct H1h2 as [[-> H1h2] | [-> H1h2]];
      destruct H2h2 as [[-> H2h2] | [-> H2h2]];
      [ iApply "HΦ"; by eauto ..|].
    (** Discharge remaining cases *)
    destruct H1h2 as (sa2we2 & h1f1 & -> & Heq1 & Hsa1orig).
    destruct H2h2 as (sa1we2 & h2f1 & -> & Heq2 & Hsa2orig).
    (** Resolve cases (T1d, _) *)
    destruct H1h1 as [-> | (sa2we0 & h1f0 & -> & Heq0 & Hsa2orig0)]; last first.
    { iMod (Writes_obs_at_origin with "[$H2Writes $H1Obs]")
        as "[H2Writes %Hle]".
      assert (length (hist_at_origin sa2
          ((h1f0 ++ [sa2we0]) ++ sa1h1f ++ [sa1we1] ++ h1f1 ++ [sa2we2]))
        ≤ length [sa2we1]) as Hle_length.
      { by apply prefix_length. }
      assert (length [sa2we1] = 1) as Hle_length1 by done.
      assert (length (hist_at_origin sa2
          ((h1f0 ++ [sa2we0]) ++ sa1h1f ++
            [sa1we1] ++ h1f1 ++ [sa2we2])) >= 2) as Hle_length2.
      { assert (length
         (hist_at_origin sa2
            ((h1f0 ++ [sa2we0]) ++ sa1h1f ++ [sa1we1] ++ h1f1 ++ [sa2we2])) =
                length
                  (hist_at_origin sa2
                    (sa2we0 :: sa2we2 :: h1f0 ++ sa1h1f ++ [sa1we1] ++ h1f1))) as Hlength_perm.
        { apply Permutation_length.
          apply filter_Permutation.
          apply symmetry.
          rewrite -!assoc.
          eapply Permutation_trans; last first.
          apply Permutation_app_swap_app.
          simpl.
          apply Permutation_skip.
          replace (h1f0 ++ sa1h1f ++ sa1we1 :: h1f1 ++ [sa2we2]) with
              ((h1f0 ++ sa1h1f ++ sa1we1 :: h1f1) ++ [sa2we2]); last first.
          { rewrite -!assoc. done. }
          rewrite (Permutation_app_comm _ [sa2we2]).
          done. }
        rewrite Hlength_perm.
        rewrite /hist_at_origin.
        rewrite filter_cons_True; [|by inversion Heq0].
        rewrite filter_cons_True; [|by inversion Heq1].
        rewrite !cons_length.
        lia. }
      lia. }
    (** Resolve cases (_, T2d) *)
    destruct H2h1 as [-> | (sa2we0 & h2f0 & -> & Heq0 & Hsa1orig0)]; last first.
    { iMod (Writes_obs_at_origin with "[$H1Writes $H2Obs]")
        as "[H1Writes %Hle]".
      assert (length (hist_at_origin sa1
          ((h2f0 ++ [sa2we0]) ++ sa2h1f ++ [sa2we1] ++ h2f1 ++ [sa1we2]))
        ≤ length [sa1we1]) as Hle_length.
      { by apply prefix_length. }
      assert (length [sa1we1] = 1) as Hle_length1 by done.
      assert (length (hist_at_origin sa1
          ((h2f0 ++ [sa2we0]) ++ sa2h1f ++ [sa2we1] ++ h2f1 ++ [sa1we2])) >= 2)
        as Hle_length2.
      { assert (length
                  (hist_at_origin sa1
                    ((h2f0 ++ [sa2we0]) ++ sa2h1f ++
                                        [sa2we1] ++ h2f1 ++ [sa1we2])) =
                length
                  (hist_at_origin sa1
                    (sa2we0 :: sa1we2 :: h2f0 ++
                            sa2h1f ++ [sa2we1] ++ h2f1))) as Hlength_perm.
        { apply Permutation_length.
          apply filter_Permutation.
          apply symmetry.
          rewrite -!assoc.
          eapply Permutation_trans; last first.
          apply Permutation_app_swap_app.
          simpl.
          apply Permutation_skip.
          replace (h2f0 ++ sa2h1f ++ sa2we1 :: h2f1 ++ [sa1we2]) with
              ((h2f0 ++ sa2h1f ++ sa2we1 :: h2f1) ++ [sa1we2]);
            [|by rewrite -!assoc].
          by rewrite (Permutation_app_comm _ [sa1we2]). }
        rewrite Hlength_perm.
        rewrite /hist_at_origin.
        rewrite filter_cons_True; [|by inversion Heq0].
        rewrite filter_cons_True; [|by inversion Heq2].
        rewrite !cons_length.
        lia. }
    lia. }
    (* Resolve case (T1b, T2b) *)
    iMod (Obs_compare with "HGInv H1Obs H2Obs") as %Hobs; [solve_ndisj|].
    rewrite !left_id in Hobs.
    destruct Hobs as [Hobs|Hobs].
    { assert (sa1h1f = sa2h1f) as <-.
      { eapply (prefix_sync_eq sa1we1 sa2we1);
          [ by eapply filter_nil_notin | by eapply filter_nil_notin | done ]. }
      apply obs_le_factor_common_prefix in Hobs.
      apply prefix_cons_inv_1 in Hobs.
      rewrite Hobs in H1mval.
      rewrite H1mval in H2mval.
      by inversion H2mval. }
    assert (sa2h1f = sa1h1f) as <-.
    { eapply (prefix_sync_eq sa2we1 sa1we1);
        [ by eapply filter_nil_notin | by eapply filter_nil_notin | done ]. }
    apply obs_le_factor_common_prefix in Hobs.
    apply prefix_cons_inv_1 in Hobs.
    rewrite Hobs in H2mval.
    rewrite H2mval in H1mval.
    by inversion H1mval.
  Qed.

End with_Σ.

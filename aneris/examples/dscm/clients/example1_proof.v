From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting adequacy.
From aneris.aneris_lang.lib Require Import par_proof.
From aneris.examples.dscm.spec Require Import base time events resources init.
From aneris.examples.dscm.clients Require Import example1_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Section Proof.
  Context `{!anerisG Mdl Σ, !spawnG Σ}.
  Context  (dbs : list socket_address) (Hdbs : NoDup dbs).

  Program Instance myparams : DB_params :=
    {| DB_addresses := dbs;
       DB_keys := {["x"; "y"]};
       DB_addresses_NoDup := Hdbs;
       DB_InvName := nroot .@ "dbinv";
       DB_serialization := int_serialization;
    |}.

  Context `{!DB_time, !DB_events, !Maximals_Computing, !DB_resources Mdl Σ}.

  Definition N := nroot.@"inv".

  Definition inv (sa : socket_address) (k1 k2 : Key) (h0 : ghst) : iProp Σ :=
    (∃ h s,
         k1 ↦ₖ{1/2} mval_of_we_opt (at_key k1 h) ∗
         k2 ↦ₖ{1/2} mval_of_we_opt (at_key k2 h) ∗
         Obs h ∗ Writes sa s ∗ ⌜h0 ≤ₚ h⌝)%I.

  Lemma inv_symm sa x y h0 :
    inv sa x y h0  -∗ inv sa y x h0.
  Proof.
    iDestruct 1 as (h s) "(Hx & Hy & #Hh & Hw & %Hle)".
    iExists _, _. iFrame. eauto.
  Qed.

  Definition thread_post (k1 k2 : Key) (h0 : ghst) : val → iProp Σ :=
    λ (vo_rd: val),
      (∃ h hf hr e0w e1w e0r vr,
           Obs h ∗
           k1 ↦ₖ{1/2} Some (mval_of_we e1w) ∗
           ⌜h = h0 ++ hf ++ [e1w] ++ hr⌝ ∗
           ⌜hist_at_key k1 h0 = [e0w]⌝ ∗
           ⌜hist_at_key k1 hf = []⌝ ∗
           ⌜hist_at_key k1 hr = []⌝ ∗
           ⌜WE_val e0w = #0⌝ ∗
           ⌜WE_val e1w = #1⌝ ∗
           ⌜at_key k2 h = Some e0r⌝ ∗ ⌜WE_val e0r = vr⌝ ∗⌜vo_rd = SOMEV vr⌝)%I.

  Lemma thread_spec sa wr rd (k1 k2 : Key) h0 (e0_wr e_rd : we) :
    {[k1; k2]} ⊆ DB_keys →
    hist_at_key k1 h0 = [e0_wr] →
    WE_val e0_wr = #0 →
    at_key k2 h0 = Some e_rd →
    GlobalInv -∗
    write_spec wr sa -∗
    read_spec rd sa -∗
    (invariants.inv N (inv sa k1 k2 h0)) -∗
    Obs h0 -∗
    k1 ↦ₖ{ 1 / 2} Some (mval_of_we e0_wr) -∗
    WP wr #k1 #1 ;; rd #k2 @[ip_of_address sa] {{ v, thread_post k1 k2 h0 v }}.
  Proof.
    iIntros "%Hkeys %He0h0 %He0v %Herdv #Hginv #Hwr_spec #Hrd_spec #Hinv #Hobs Hkwr".
    iApply aneris_wp_fupd.
    (* Symbolic execution of write. *)
    wp_bind (wr _ _).
    iDestruct (write_spec_write_spec_atomic with "Hwr_spec") as "Hwr_spec'".
    unshelve iApply ("Hwr_spec'" $! k1 (SerVal #1) _ _ (⊤∖↑N));
      [ eauto with set_solver | solve_ndisj | ].
    (* Proving the write precondition *)
    iInv N as ">Hri" "Hcl".
    iDestruct "Hri" as (h1 s1) "(Hkwr2 & Hkrd1 & #HobsInv & Hw & [%h0f %Hh1eq])".
    iMod (OwnMemKey_obs_frame_prefix_some k1 _ h0 h1 e0_wr
            with "[$Hkwr $HobsInv]") as "(Hkwr1 & %Hk10f)";
      [ solve_ndisj | list_simplifier; by apply prefix_app_r |
        rewrite /at_key; rewrite He0h0; by simplify_list_eq | done | ].
    iPoseProof (OwnMemKey_combine with "[$Hkwr2 $Hkwr1]") as "(Hkwr & %Hkwrv_eq)".
    eauto. rewrite Hkwrv_eq.
    iExists h1, s1, (at_key k1 h1).
    rewrite Hkwrv_eq. rewrite Qp.half_half. iFrame "Hkwr Hw HobsInv". simpl in *.
    iIntros "!#!>".
    iSplit; [ done | ].
    iIntros (hkwr1f ewr1) "(%Hkwr1f & %Hkwr1k & %Hkwr1v & %Hkwr1o & %Hkwr1t & Hkwr & #Hkwr1Obs & Hw)".
    rewrite -{4}Qp.half_half.
    iPoseProof (OwnMemKey_split k1 (1/2)%Qp (1/2)%Qp with "[$Hkwr]") as "(Hkwr1 & Hkwr2)".
    iMod (OwnMemKey_allocated k2 _ h0 h1 e_rd with "[$Hkrd1 //]") as (erd) "(Hkrd1 & %Herdh1 & %Hrde0e1)";
      [ solve_ndisj | list_simplifier; by apply prefix_app_r | by simplify_list_eq |  ].
    iMod (OwnMemKey_obs_frame_prefix_some k2 (1/2)%Qp h1 (h1 ++ hkwr1f ++ [ewr1]) erd
            with "[Hkrd1 $Hkwr1Obs]") as "(Hrd1 & %Herd1)";
      [solve_ndisj| by apply prefix_app_r | done | done | rewrite Herdh1; iFrame | ].
    iMod ("Hcl" with "[Hkwr2 Hrd1 Hw]") as "_".
    iNext. iExists (h1 ++ hkwr1f ++ [ewr1]), (s1 ++ [ewr1]).
    iFrame "Hkwr1Obs Hw". rewrite {2}app_assoc.
    rewrite (mval_of_we_opt_at_key_some ewr1 k1 (h1 ++ hkwr1f)).
    rewrite Herd1. iFrame. iPureIntro. rewrite Hh1eq. by list_simplifier; apply prefix_app_r. done.
    iModIntro. wp_pures.
    (* Clean up *)
    clear s1 Herdh1 Hrde0e1 Herd1 erd.
    (* Symbolic execution of read *)
    iDestruct (read_spec_read_spec_atomic rd sa with "[Hrd_spec]") as "Hrd_spec'".
    { iApply "Hrd_spec". }
    unshelve iApply ("Hrd_spec'" $! k2 _ _ (⊤∖↑N));
      [ eauto with set_solver | solve_ndisj | ] .
    iInv N as ">Hri" "Hcl".
    iDestruct "Hri" as (h2 s1) "(Hkwr2 & Hkrd1 & #HobsInv_rd & Hw & %Hh0h2)".
    iMod (Obs_lub with "[$Hginv] [$HobsInv_rd] [$Hkwr1Obs]") as (h3) "(%Hh3le1 & %Hh3le2 & #Hobsh3)";
      [solve_ndisj |].
    iPoseProof (OwnMemKey_combine with "[$Hkwr1 $Hkwr2]") as "(Hkwr & %Hwreq)".
    iExists h3, (1/2)%Qp, (at_key k2 h2).
    iMod (OwnMemKey_allocated k2 _ h0 h2 e_rd with "[$Hkrd1 //]") as (erd) "(Hkrd1 & %Herdh1 & %Hrde0e1)";
      [ solve_ndisj | done | by simplify_list_eq |  ].
    iMod (OwnMemKey_obs_frame_prefix k2 _ h2 h3 with "[$Hkrd1 $Hobsh3]") as "(Hkrd1 & %Hrdh2h3)";
      [ by solve_ndisj | done |].
    rewrite Hrdh2h3.
    iMod (OwnMemKey_allocated k2 _ h0 h3 e_rd with "[$Hkrd1]") as (erd') "(Hkrd1 & %Herdh2 & _)";
      [ solve_ndisj | by apply (PreOrder_Transitive h0 h2 h3) | by simplify_list_eq | ].
    iFrame "Hobsh3 Hkrd1". do 2 iModIntro.
    iSplit; [done|].
    iIntros "H".
    iDestruct "H" as "[[%Heq Hk] | H]".
    { rewrite Heq in Hrdh2h3.
      rewrite Hrdh2h3 in Herdh1.
      done. }
    iDestruct "H" as (e Heq) "Hkrd".
    iPoseProof (OwnMemKey_split k1 (1/2)%Qp (1/2)%Qp with "[$Hkwr]") as "(Hkwr1 & Hkwr2)".
    iMod ("Hcl" with "[Hkwr2 Hkrd Hw]") as "_". iNext.
    iExists h2, s1. rewrite Hwreq Hrdh2h3 Heq. iFrame. iFrame "HobsInv_rd". eauto.
    (* Proving postcondition. *)
    destruct Hh0h2 as (hr & Hrdh).
    destruct Hh3le2 as (hr0 & Hh3eq).
    iMod (OwnMemKey_some_obs_frame k1 _ ewr1 (h0 ++ h0f ++ hkwr1f) hr0
            with "[$Hkwr1]") as "(Hkwr1 & %Hk1hr0)";
      [solve_ndisj| | ].
    { assert (((h0 ++ h0f) ++ hkwr1f ++ [ewr1]) ++ hr0 = (h0 ++ h0f ++ hkwr1f) ++ [ewr1] ++ hr0) as Hh3eq'.
      { by list_simplifier. }
      rewrite Hh3eq Hh1eq -Hh3eq'. iFrame "Hobsh3". }
    iModIntro.
    iExists h3, (h0f ++ hkwr1f), hr0, e0_wr, ewr1, erd, (WE_val erd).
    assert (e = erd). { rewrite Hrdh2h3 in Herdh1. naive_solver. }
                      assert (hist_at_key k1 (h0f ++ hkwr1f) = hist_at_key k1 h0f ++ hist_at_key k1 hkwr1f) as Hfiltapp.
    { rewrite /hist_at_key. by apply filter_app. }
    iFrame "Hkwr1 Hobsh3".
    rewrite Hh1eq.
    iMod (Obs_ext_hist h0 (h0++h0f) k1 _ with "[//] [//] [$HobsInv $Hobs]") as "%Hk1h0le";
      first by solve_ndisj. rewrite -Hh1eq Hk10f /at_key He0h0. done.
    iModIntro.
    repeat (iSplit; first (iPureIntro; eauto)).
    - by list_simplifier.
    - rewrite Hfiltapp.
      assert (hist_at_key k1 hkwr1f = []) as He1f.
      { by apply hist_at_key_empty_at_key. }
      assert (hist_at_key k1 h0f = []) as Hh0e0.
      { apply (obs_le_at_key_hist_at_key h0 h0f h1).
        done. naive_solver. }
      by rewrite He1f Hh0e0.
    - by apply last_None.
    - naive_solver.
    - destruct (at_key k2 h3); naive_solver.
  Qed.

  Lemma prog_spec sa wr rd :
    sa ∉ DB_addresses →
    GlobalInv -∗
    write_spec wr sa -∗
    read_spec rd sa -∗
    {{{ Obs [] ∗ "x" ↦ₖ None ∗ "y" ↦ₖ None ∗ Writes sa [] }}}
      par_prog wr rd @[ip_of_address sa]
    {{{ (v : val), RET v; ⌜v = (SOMEV #0, SOMEV #1)%V⌝ ∨
                          ⌜v = (SOMEV #1, SOMEV #0)%V⌝ ∨
                          ⌜v = (SOMEV #1, SOMEV #1)%V⌝}}}.
  Proof.
    iIntros "%Hsa #Hginv #Hwr_spec #Hrd_spec" (Φ).
    iAssert ((write_spec wr sa)%I) as "Hwr_spec_copy"; eauto.
    iAssert ((read_spec rd sa)%I) as "Hrd_spec_copy"; eauto.
    iModIntro.
    iIntros "(#Hobs & Hx & Hy & Hw) HΦ". wp_pures.
    iDestruct (get_simplified_write_spec with "Hwr_spec") as "Hswr".

    (* Symbolic execution of "wr x 0". *)
    wp_bind (wr _ _).
    wp_apply ("Hswr" $! "x" (SerVal #0) [] [] with "[] [$Hx $Hobs $Hw]"); [done |].
    (* -- Postcondition of write spec *)
    iClear "Hobs".
    iDestruct 1 as (hx0f x0) "(%Hx0k & %Hx0v & %Hx0o & %Hx0f & #Hobs & Hx & Hw)".

    (* Symbolic execution of "wr y 0". *)
    wp_pures. wp_bind (wr _ _). simpl in *.
    iMod (OwnMemKey_none_obs with "[$Hy Hobs]") as "(Hy & %HyNone)"; [set_solver| eauto|].
    wp_apply ("Hswr" $! "y" (SerVal #0) _ _  with "[] [$Hobs $Hw Hy]");
      [done|by rewrite mval_of_we_opt_at_key_none|].
    (* -- Postcondition of write spec *)
    iClear "Hobs".
    iDestruct 1 as (hy0f y0) "(%Hy0k & %Hy0v & %Hy0o & %Hy0f & #Hobs & Hy & Hw)".

    (* Split resources. *)
    wp_pures. simpl in *. rewrite -Qp.half_half.
    iDestruct (fractional_split_1 ("x" ↦ₖ{_} Some (mval_of_we x0))%I
                 with "[$Hx]") as "(Hx1 & Hx2)".
    iDestruct (fractional_split_1 ("y" ↦ₖ{_} Some (mval_of_we y0))%I
                 with "[$Hy]") as "(Hy1 & Hy2)".
    set (h0 := (hx0f ++ [x0]) ++ hy0f ++ [y0]).
    (* hfy ++ [y0 ] is frame for x0. *)
    iMod (OwnMemKey_obs_frame_prefix_some
            "x" (1/2) (hx0f ++ [x0]) h0 x0 with "[$Hx1 $Hobs]") as "(Hx1 & %Hxh0)";
      [set_solver | by apply prefix_app_r | by apply at_key_snoc_some  | done |].
    iMod (OwnMemKey_some_obs_frame "x" (1/2) x0 hx0f (hy0f ++ [y0]) _ with
              "[$Hx1 Hobs]") as "(Hx1 & %Hx0fr)";
      [set_solver | rewrite /h0; list_simplifier; eauto with iFrame | ].
    assert (hist_at_key "x" h0 = [x0]) as Hxh0x0.
    { rewrite /h0. rewrite app_assoc.
      rewrite hist_at_key_frame_r_singleton; last by rewrite Hy0k.
      rewrite hist_at_key_frame_r_suffix.
      rewrite hist_at_key_frame_l_prefix; last done.
      by rewrite hist_at_key_some_singleton.
      apply hist_at_key_empty_at_key.
      apply hist_at_key_empty_at_key in Hx0fr.
      rewrite hist_at_key_app in Hx0fr.
      list_simplifier. erewrite app_nil in Hx0fr.
      by destruct Hx0fr. }
   assert (hist_at_key "y" h0 = [y0]) as Hyh0y0.
    { rewrite /h0. rewrite app_assoc.
      rewrite hist_at_key_frame_l_prefix.
      rewrite hist_at_key_singleton.
      rewrite -Hy0k. by rewrite at_key_singleton.
      rewrite -hist_at_key_empty_at_key.
      by rewrite hist_at_key_frame_r_suffix. }

    (* Allocate the invariant. *)
    iMod (inv_alloc N _ (inv sa "x" "y" h0) with "[Hx2 Hy2 Hobs Hw]") as "#Hinv".
    iExists h0, _. rewrite Hxh0. iFrame.
    assert (h0 = ((hx0f ++ [x0]) ++ hy0f) ++ [y0]) as Hh0eq.
    {  rewrite /h0; by list_simplifier. }
    rewrite {2} Hh0eq (at_key_snoc_some "y" ((hx0f ++ [x0]) ++ hy0f) y0 Hy0k).
    by iFrame; iFrame "#".
    iApply aneris_wp_fupd.
    assert (at_key "y" h0 = Some y0) as Hyh0y0'.
    { rewrite /at_key Hyh0y0. by apply last_singleton. }
    iPoseProof (inv_iff N _ (inv sa "y" "x" h0) with "[$Hinv] []") as "Hinv'".
      { iIntros "!> !#"; iSplit; iIntros "HinvP"; by iApply inv_symm. }

    (* Parallel composition. *)
    iApply (wp_par _ (thread_post "x" "y" h0) (thread_post "y" "x" h0) with "[Hx1] [Hy1] [HΦ]").
    (* Left thread. *)
    - iApply (thread_spec _ _ _ _ _ _ x0 y0 with "[][][][$Hinv][][$Hx1]"); eauto.
    (* Right thread. *)
    -  iApply (thread_spec sa wr rd _ _ _ y0 x0 with "[][][][Hinv][][Hy1]");
        [ set_solver | eauto.. ].

    (* Postcondition. *)
    - iIntros (v1 v2) "(HΨ1 & HΨ2)".
      iClear "Hswr Hobs Hrd_spec Hwr_spec".
      iDestruct "HΨ1"
        as (h1 hf1 hr1 ex0 ex1 eyrd y1v)
             "(#HobsL & Hx1 & %Hh1 & %Hx1h0 & %Hx1hf & %Hx1hr & %Hx0'v & %Hx1v & %Hy1h1 & %Hy1v & %Hv1y1)".
      iDestruct "HΨ2"
        as (h2 hf2 hr2 ey0 ey1 exrd x2v)
             "(#HobsR & Hy2 & %Hh2 & %Hy2h0 & %Hy2hf & %Hy2hr & %Hy2'v & %Hy2v & %Hx2h2 & %Hx2v & %Hv2x2)".
      iNext. iApply "HΦ".
      iPoseProof (Obs_compare h1 h2 with "[] [$HobsL] [$HobsR]") as ">Hdisj"; eauto.
      iMod (OwnMemKey_key with "[$Hx1]") as "(Hx1 & %Hx1k)"; first by solve_ndisj.
      iMod (OwnMemKey_key with "[$Hy2]") as "(Hy2 & %Hy2k)"; first by solve_ndisj.
      assert (ex0 = x0) as Hex0eq.
      { rewrite Hx1h0 in Hxh0x0. by inversion Hxh0x0. }
      assert  (hist_at_key "x" h1 = [x0; ex1]) as HxH1.
      { rewrite Hh1.
        rewrite hist_at_key_app.
        rewrite Hxh0x0.
        f_equal.
        rewrite hist_at_key_frame_l_prefix; last by apply hist_at_key_empty_at_key.
        rewrite hist_at_key_frame_r_suffix; last by apply hist_at_key_empty_at_key.
        apply hist_at_key_some_singleton; last eauto. }
      assert (ey0 = y0) as Hey0eq.
      { rewrite Hy2h0 in Hyh0y0. by inversion Hyh0y0. }
      assert  (hist_at_key "y" h2 = [ey0; ey1]) as Hyh2.
      { rewrite Hh2.
        rewrite hist_at_key_app.
        rewrite Hyh0y0 Hey0eq.
        f_equal.
        rewrite hist_at_key_frame_l_prefix; last by apply hist_at_key_empty_at_key.
        rewrite hist_at_key_frame_r_suffix; last by apply hist_at_key_empty_at_key.
        apply hist_at_key_some_singleton; last eauto. }
      iDestruct "Hdisj" as "[%Hp|%Hp]".
      + rewrite Hv1y1 Hv2x2.
        assert ( mval_of_we_opt (at_key "x" h1) = Some (mval_of_we ex1)) as <-.
        { rewrite /at_key HxH1. by list_simplifier. }
        iPoseProof (OwnMemKey_obs_frame_prefix "x" with "[$Hx1] ") as ">(Hx1 & %Heq)"; eauto with iFrame.
        assert (Some ex1 = Some exrd) as Hex1exrd.
        { rewrite -Hx2h2 -Heq /at_key HxH1. by list_simplifier. }
        rewrite -Hx2v.
        injection Hex1exrd as Heq'. rewrite -Heq' Hx1v.
        assert (y1v = #0 ∨ y1v = #1) as [-> | ->]; [| iModIntro; eauto 42.. ].
        { specialize (obs_le_hist_at_key_le _ _ "y" Hp) as Hy.
          assert (eyrd ∈ (hist_at_key "y" h2)) as Heyrdh2.
          { eapply at_key_le_in; eauto. }
          rewrite Hyh2 in Heyrdh2.
          set_solver. }
      + rewrite Hv1y1 Hv2x2.
        assert ( mval_of_we_opt (at_key "y" h2) = Some (mval_of_we ey1)) as <-.
        { rewrite /at_key Hyh2. by list_simplifier. }
        iPoseProof (OwnMemKey_obs_frame_prefix "y" with "[$Hy2] ") as ">(Hy2 & %Heq)";
          eauto with iFrame.
        assert (Some ey1 = Some eyrd) as Hey1eyrd.
        { rewrite -Hy1h1 -Heq /at_key Hyh2. by list_simplifier. }
        rewrite -Hy1v.
        injection Hey1eyrd as Heq'. rewrite -Heq' Hy2v.
        assert (x2v = #0 ∨ x2v = #1) as [Hx2v0 | Hx2v1]; [| iModIntro; eauto 42.. ].
        { specialize (obs_le_hist_at_key_le _ _ "x" Hp) as Hx.
          assert (exrd ∈ (hist_at_key "x" h1)) as Hexrdh2.
          { eapply at_key_le_in; eauto. }
          rewrite HxH1 in Hexrdh2.
          set_solver. }
        * rewrite Hx2v0. eauto.
        * rewrite Hx2v1. eauto.
  Qed.

End Proof.

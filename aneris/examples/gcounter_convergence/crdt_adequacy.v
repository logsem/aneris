From iris.algebra Require Import auth excl csum gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.prelude Require Import gset_map time.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import network resources proofmode adequacy.
From aneris.aneris_lang.lib Require Import inject list_proof vector_clock_proof.
From aneris.examples.gcounter_convergence Require Import
     crdt_model crdt_resources crdt_proof crdt_main_rel crdt_runner.

Lemma helper gcdata (ps : programs_using_gcounters gcdata) :
  ∀ a : socket_address,
    a ∈ list_to_set (C := gset _) (gcd_addr_list gcdata) ∪ Aprogs ps
    → ip_of_address a ∈ list_to_set (C := gset _) (ip_of_address <$> gcd_addr_list gcdata).
Proof.
  intros a.
  rewrite elem_of_union !elem_of_list_to_set elem_of_list_fmap.
  intros [|(?&?&?)%Aprogs_on_nodes]; by eauto.
Qed.

(* move*)
#[global] Instance Helper_instance_1: Inj eq eq (λ i : nat, StringOfZ i).
Proof.
  intros ? ? ?.
  assert (Some (N.of_nat x) = Some (N.of_nat y)); last by simplify_eq.
  rewrite -!ZOfString'_inv.
  f_equal; done.
Qed.

Lemma gcounter_safety gcdata (ps : programs_using_gcounters gcdata) :
  safe (mkExpr "system" (runner gcdata 0 (progs ps) $(gcd_addr_list gcdata))) init_state.
Proof.
  eapply (@adequacy_safe
            #[anerisΣ (GCounterM gcdata); GCounterΣ gcdata; progs_Σ ps]
            (GCounterM gcdata)
            _
            _
            (list_to_set (ip_of_address <$> gcd_addr_list gcdata))
            (list_to_set (gcd_addr_list gcdata) ∪ (Aprogs ps))
            (list_to_set ((λ i : nat, StringOfZ i) <$> seq 0 (GClen gcdata)))
            (list_to_set (gcd_addr_list gcdata))
            (list_to_set (gcd_addr_list gcdata))).
  { apply GcounterM_rel_finitary. }
  { intros ?.
    iMod (runner_spec with "[]") as (?) "Hwp".
    - apply ps.
    - apply ps.
    - apply is_list_inject; eauto.
    - apply ps.
    - apply ps.
    - apply ps.
    - iPoseProof (progs_wp ps) as "?"; done.
    - iModIntro.
      iIntros "Hfx Hmps Hfst Hfips Hins Halevs Hsevs Hrevs _ _".
      iModIntro.
      iApply (wp_wand _ _ _ _ (λ w, ∃ v, ⌜w = mkVal "system" v⌝ ∗ True)%I with "[-]"); [|done].
      iApply (aneris_wp_lift with "Hins").
      iMod ("Hwp" with "Hfst Hfx [Hmps] [Hsevs] [Hrevs] [Hfips] [Halevs]") as "[#Hinv Hwp]".
      + assert (Aprogs ps = (⋃ (portssocks ps).*2)) as -> by apply ps. done.
      + by rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup.
      + by rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup.
      + rewrite big_sepS_list_to_set; last by apply gcd_addr_list_NoDup_ips.
        rewrite big_sepL_fmap; done.
      + rewrite big_sepS_list_to_set; last (apply NoDup_fmap; [apply _|apply NoDup_seq]).
        rewrite big_sepL_fmap; done.
      + by iApply (aneris_wp_wand with "Hwp"). }
  { set_solver. }
  { set_solver. }
  { rewrite elem_of_list_to_set elem_of_list_fmap; intros [? [? [? ?]%elem_of_list_lookup]].
    eapply gcd_addr_list_nonSys; eauto. }
  { done. }
  { done. }
  { done. }
Qed.

Lemma gcounter_adequacy gcdata (ps : programs_using_gcounters gcdata) :
  @continued_simulation aneris_lang (aneris_to_trace_model (GCounterM gcdata))
    (crdt_main_rel gcdata)
    {tr[ ([mkExpr "system" (runner gcdata 0 (progs ps) $(gcd_addr_list gcdata))],
          init_state) ]}
    {tr[ initial_crdt_state (GClen gcdata) ]}.
Proof.
  eapply (simulation_adequacy
            #[anerisΣ (GCounterM gcdata); GCounterΣ gcdata; progs_Σ ps]
            (GCounterM gcdata)
            NotStuck
            (list_to_set (ip_of_address <$> gcd_addr_list gcdata))
            (list_to_set ((λ i : nat, StringOfZ i) <$> seq 0 (GClen gcdata)))
            (list_to_set (gcd_addr_list gcdata) ∪ (Aprogs ps))
            (list_to_set (gcd_addr_list gcdata))
            (list_to_set (gcd_addr_list gcdata))
            (λ _, True) _ _ _ (init_state)).
  { set_solver. }
  { set_solver. }
  { apply aneris_sim_rel_finitary, GcounterM_rel_finitary. }
  { rewrite elem_of_list_to_set elem_of_list_fmap; intros [? [? [? ?]%elem_of_list_lookup]].
    eapply gcd_addr_list_nonSys; eauto. }
  { done. }
  { done. }
  { done. }
  iIntros (?) "".
  iMod (runner_spec with "[]") as (?) "Hwp".
  { apply ps. }
  { apply ps. }
  { apply is_list_inject; eauto. }
  { apply ps. }
  { apply ps. }
  { apply ps. }
  { iPoseProof (progs_wp ps) as "?"; done. }
  iModIntro.
  iExists (λ v, ∃ w : val, ⌜v = _⌝ ∗ ⌜w = #()⌝)%I.
  iIntros "Hfx Hmps Hfips Hins Halevs Hsevs Hrevs _ _ Hfst".
  iMod ("Hwp" with "Hfst Hfx [Hmps] [Hsevs] [Hrevs] [Hfips] [Halevs]") as "[#Hinv Hwp]".
  { assert (Aprogs ps = (⋃ (portssocks ps).*2)) as -> by apply ps. done. }
  { by rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup. }
  { by rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup. }
  { rewrite big_sepS_list_to_set; last by apply gcd_addr_list_NoDup_ips.
    rewrite big_sepL_fmap; done. }
  { rewrite big_sepS_list_to_set;
    last (apply NoDup_fmap; [apply _|apply NoDup_seq]).
    rewrite big_sepL_fmap; done. }
  iModIntro.
  iSplitR; first done.
  iSplitL.
  { rewrite aneris_wp_unfold /aneris_wp_def. iApply "Hwp"; done. }
  iIntros (ex atr c' Hvls Hexs Hatrs Hexe Hlast _) "HSI _".
  destruct (valid_system_trace_start_or_contract ex atr) as [[-> ->]|Hcontr]; first done.
  - erewrite !first_eq_trace_starts_in; [|eassumption|eassumption].
    iMod fupd_mask_subseteq as "_"; [|iModIntro]; first done.
    iPureIntro.
    apply crdt_main_rel_initially.
  - destruct Hcontr as (ex' & atr' & oζ & ℓ & Hex'& Hatr').
    destruct (Hlast ex' atr' oζ ℓ) as [Hmrel Hvse]; [done|done|].
    iInv CvRDT_InvName as (st locs sevss revss)
      ">(Hfst & HGC & Hlocs & Hsevss & Hrevss & Hlocs_coh & Hsevss_coh & Hrevss_coh & Hnet)"
      "_".
    iMod fupd_mask_subseteq as "_"; [|iModIntro]; first done.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %Hlocslen.
    iAssert (⌜∀ i, locs_of_trace_now gcdata ex !! i = locs !! i⌝)%I as %Hlocs.
    { iIntros (i).
      destruct (decide (i < GClen gcdata)) as [Hlt|]; last first.
      { rewrite [_ _ _ !! _]lookup_ge_None_2; last by rewrite locs_of_trace_now_length; lia.
        iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
        rewrite lookup_ge_None_2; last lia. done. }
      destruct (lookup_lt_is_Some_2 locs i) as [ol Hol]; first lia.
      iDestruct (locations_coherence_insert_acc (nat_to_fin Hlt) with "Hlocs_coh")
        as "[Hcohl _]"; first by rewrite fin_to_nat_to_fin.
      iDestruct "HSI" as "[HSI_evs _]".
      iDestruct "HSI_evs" as (AS Ar lbls) "(_ & _ & _ & _ & _ & Halevs)".
      destruct ol as [l|]; simpl.
      - iDestruct "Hcohl" as (a Ha) "[Hcohl Hl]".
        iDestruct "Hcohl" as (σ h Hvlev) "Hevs".
        iDestruct (alloc_evs_lookup with "Halevs Hevs") as %Halloc.
        apply lookup_fn_to_gmap in Halloc as [Halloc ?].
        eapply (locs_of_trace_now_lookup_singleton gcdata) in Halloc;
          last by rewrite fin_to_nat_to_fin.
        rewrite fin_to_nat_to_fin in Halloc.
        rewrite Halloc Hol; done.
      - iDestruct "Hcohl" as "[Hevs _]".
        iDestruct (alloc_evs_lookup with "Halevs Hevs") as %Halloc.
        apply lookup_fn_to_gmap in Halloc as [Halloc ?].
        eapply (locs_of_trace_now_lookup_nil gcdata) in Halloc;
          last by rewrite fin_to_nat_to_fin.
        rewrite fin_to_nat_to_fin in Halloc.
        rewrite Halloc Hol; done. }
    apply list_eq in Hlocs.
    iAssert (⌜trace_last atr = st⌝)%I as %Heqst.
    { iDestruct "HSI" as "(_ & Hsi & Hast & % & ?)".
      iDestruct (auth_frag_st_agree with "Hast Hfst") as %<-; done. }
    iAssert (⌜∀ (i : fin (GClen gcdata)) (l : loc), locs !! (fin_to_nat i) = Some (Some l) →
              ∃ h : heap, state_heaps (trace_last ex).2 !!
                           ip_of_address (gcd_addr_list gcdata !!! (fin_to_nat i)) = Some h ∧
                h !! l = Some (vector_clock_to_val (vec_to_list (st !!! i)))⌝)%I
      as %Hhlu.
    { iIntros (i l Hl).
      iDestruct "HSI" as "(_ & Hsi & _)".
      iDestruct (locations_coherence_insert_acc i with "Hlocs_coh") as "[Hcohl _]";
        first by eauto.
      iDestruct "Hcohl" as (a Ha) "[Hcohl Hl]".
      iDestruct "Hcohl" as (σ h Hvlev) "Hevs".
      iDestruct (aneris_state_interp_heap_valid with "Hsi Hl") as (h') "[%Hh'1 %Hh'2]".
      erewrite list_lookup_total_correct; last eassumption.
      eauto. }
    iAssert
      (⌜∀ i : fin (length (gcd_addr_list gcdata)),
        match locs_of_trace_now gcdata ex !!! (fin_to_nat i) with
        | Some l =>
            ∃ h : heap,
            (trace_last ex).2.(state_heaps) !!
                ip_of_address (gcd_addr_list gcdata !!! (fin_to_nat i)) = Some h ∧
            h !! l =
              Some (vector_clock_to_val (vec_to_list ((trace_last atr) !!! i)))
        | None => (trace_last atr) !!! i = vreplicate (length (gcd_addr_list gcdata)) 0
       end⌝)%I as %Hvalrel.
    { rewrite Hlocs.
      iIntros (i).
      destruct (lookup_lt_is_Some_2 locs i) as [ol Hol];
        first by rewrite Hlocslen; apply fin_to_nat_lt.
      iDestruct (locations_coherence_insert_acc i with "Hlocs_coh") as "[Hcohl _]";
        first eassumption.
      erewrite list_lookup_total_correct; last eassumption.
      rewrite Heqst.
      destruct ol; first by auto.
      iDestruct "Hcohl" as "[? ?]"; done. }
    iAssert (⌜send_evs_rel gcdata (locs_of_trace_now gcdata ex) ex⌝)%I as %Hsevss.
    { iExists sevss.
      iDestruct (sendevs_coherence_length with "Hsevss_coh") as %?.
      iSplit; first by iPureIntro; lia.
      iIntros (i Hi).
      destruct (lookup_lt_is_Some_2 locs i) as [ol Hol]; first lia.
      destruct (lookup_lt_is_Some_2 sevss i) as [sevs Hsevs]; first lia.
      iDestruct (sendevs_coherence_insert_acc with "Hsevss_coh") as "[Hcohs _]";
        [eassumption|eassumption|].
      iExists sevs.
      iSplit; first done.
      iDestruct "Hcohs" as (a Ha) "[% [_ Hcohs]]".
      iSplit; first done.
      rewrite Hlocs.
      repeat (erewrite list_lookup_total_correct; last eassumption).
      iDestruct "HSI" as "(Hevs & _)".
      iDestruct "Hevs" as (As Ar lbls) "(_ & _ & _ & Hsevs & _ & _)".
      destruct ol as [l|].
      - iDestruct "Hcohs" as (evs) "[Hevs %]".
        iDestruct (sendon_evs_lookup with "Hsevs Hevs") as %Hevs.
        apply lookup_fn_to_gmap in Hevs as [<- ?]; done.
      - iDestruct "Hcohs" as "[Hevs ->]".
        iDestruct (sendon_evs_lookup with "Hsevs Hevs") as %Hevs.
        apply lookup_fn_to_gmap in Hevs as [<- ?]; done. }
    iAssert (⌜receive_evs_rel gcdata (locs_of_trace_now gcdata ex) ex⌝)%I as %Hrevss.
    { iExists revss.
      iDestruct (recevs_coherence_length with "Hrevss_coh") as %?.
      iSplit; first by iPureIntro; lia.
      iIntros (i Hi).
      destruct (lookup_lt_is_Some_2 locs i) as [ol Hol]; first lia.
      destruct (lookup_lt_is_Some_2 revss i) as [revs Hrevs]; first lia.
      iDestruct (recevs_coherence_insert_acc with "Hrevss_coh") as "[Hcohr _]";
        [eassumption|].
      iExists revs.
      iSplit; first done.
      iDestruct "Hcohr" as (a evs) "[% (Happlied & Hnea & Hrevs & Hcorr)]".
      rewrite Hlocs.
      repeat (erewrite list_lookup_total_correct; last eassumption).
      iDestruct "HSI" as "(Hevs & _ & _)".
      iDestruct "Hevs" as (As Ar lbls) "(_ & _ & _ & _ & Hrvs & _)".
      iDestruct (receiveon_evs_lookup with "Hrvs Hrevs") as %Hevs.
      apply lookup_fn_to_gmap in Hevs as [<- ?].
      destruct ol as [l|].
      - destruct (Hhlu (nat_to_fin Hi) l) as (h & Hh1 & Hh2);
          first by rewrite fin_to_nat_to_fin.
        rewrite fin_to_nat_to_fin in Hh1.
        erewrite list_lookup_total_correct in Hh1; last eassumption.
        iSplit; first done.
        iExists _, _; iSplit; first done.
        iSplit; first done.
        iIntros (j rev Hj Hrev).
        iSpecialize ("Happlied" $! rev j Hj Hrev).
        iApply (GCounterSnapShot_le with "[Happlied] HGC"); by rewrite fin_to_nat_to_fin.
      - rewrite /receiveonEV.
        destruct (events_of_trace (receiveonEV_groups {[a]}) ex) eqn:Heq.
        { rewrite Heq. iDestruct "Hcorr" as %->%Forall2_nil_inv_l; done. }
        rewrite Heq. iDestruct ("Hnea" with "[//]") as (l) "Hl".
        iDestruct (locations_is_allocated with "Hlocs Hl") as %?; simplify_eq. }
    iDestruct "HSI" as "(?&?&?&%&?)".
    iPureIntro.
    eapply crdt_main_rel_step; eauto.
    inversion Hatr'; simplify_eq; eauto.
Qed.

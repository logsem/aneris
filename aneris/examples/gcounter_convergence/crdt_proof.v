From iris.algebra Require Import auth excl csum gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import inject list_proof vector_clock_proof network_util_proof.
From aneris.examples.gcounter_convergence Require Import
     crdt_code crdt_model crdt_resources vc.


Section specification.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.

  (** General specifications for read & write *)

  Definition query_spec (GCounter : nat → nat → iProp Σ)
       (query : val) (i: nat) (a : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ n : nat,
        ⌜gcd_addr_list gcdata !! i = Some a⌝ -∗
          {{{  GCounter i n }}}
          query #() @[ip_of_address a]
          {{{ m, RET #m; ⌜n <= m⌝ ∗ GCounter i m }}})%I.

  Definition incr_spec (GCounter : nat → nat → iProp Σ)
      (incr : val) (i: nat) (a : socket_address)  : iProp Σ :=
    Eval simpl in
    □ (∀ n: nat,
        ⌜gcd_addr_list gcdata !! i = Some a⌝ -∗
        {{{ GCounter i n }}}
          incr #() @[ip_of_address a]
        {{{ RET #(); ∃ m, ⌜n < m⌝ ∗ GCounter i m }}})%I.

End specification.

Section proof.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.

  Fixpoint vector_clock_merge (l1 l2 : list nat) : list nat :=
    match l1, l2 with
    | [], l | l, [] => l
    | x :: l, y :: k =>  max x y :: vector_clock_merge l k
    end.

  Lemma vector_clock_merge_lookup l1 l2 i :
    length l1 = length l2 →
    vector_clock_merge l1 l2 !! i = (l1 !! i) ≫= (λ x, (l2 !! i) ≫= (λ y, Some (x `max` y))).
  Proof.
    revert i l2; induction l1 as [|a l1 IHl1]; intros i l2 Hlen.
    { destruct l2; done. }
    destruct l2 as [|b l2]; first done.
    destruct i; first done.
    apply IHl1; auto.
  Qed.

  Lemma vector_clock_merge_length n l1 l2 :
    length l1 = n → length l2 = n → length (vector_clock_merge l1 l2) = n.
  Proof.
    revert l1 l2; induction n as [|n IHn]; intros l1 l2 Hl1 Hl2.
    { destruct l1; destruct l2; done. }
    destruct l1 as [|a l1]; first done.
    destruct l2 as [|b l2]; first done.
    simpl in *.
    rewrite IHn; auto.
  Qed.

  Lemma vector_clock_merge_le l1 l2 :
    length l1 = length l2 → vector_clock_le l1 (vector_clock_merge l1 l2).
  Proof.
    revert l2; induction l1 as [|a l1 IHl1]; intros l2 Hlen.
    - destruct l2; last done. constructor.
    - destruct l2; first done.
      simpl; constructor; first lia.
      apply IHl1; auto.
  Qed.

  Lemma vector_clock_le_vc_le n (vc1 vc2 : vector_clock n) :
    vector_clock_le vc1 vc2 → vc_le vc1 vc2.
  Proof.
    rewrite /vector_clock_le Forall2_lookup.
    intros Hle i.
    specialize (Hle i).
    assert (vec_to_list vc1 !! (fin_to_nat i) = Some (vc1 !!! i)) as Heq1
        by by rewrite -vlookup_lookup.
    assert (vec_to_list vc2 !! (fin_to_nat i) = Some (vc2 !!! i)) as Heq2
        by by rewrite -vlookup_lookup.
    rewrite Heq1 Heq2 in Hle.
    inversion Hle; simplify_eq; done.
  Qed.

  Lemma vc_mrge_lookup n (vc1 vc2 : vector_clock n) i :
    vc_merge vc1 vc2 !!! i = vc1 !!! i `max` vc2 !!! i.
  Proof. apply vlookup_zip_with. Qed.

  Lemma vector_clock_merge_vc_merge n l1 (vc1 : vector_clock n) l2 (vc2 : vector_clock n) :
    vec_to_list vc1 = l1 →
    vec_to_list vc2 = l2 →
    vector_clock_merge l1 l2 = vec_to_list (vc_merge vc1 vc2).
  Proof.
    intros Hl1 Hl2.
    apply list_eq; intros i.
    rewrite vector_clock_merge_lookup; last by rewrite -Hl1 -Hl2 !vec_to_list_length.
    destruct (decide (i < n)) as [Hlt|Hnlt].
    - pose (fi := nat_to_fin Hlt).
      destruct (lookup_lt_is_Some_2 l1 i) as [x Hx]; first by rewrite -Hl1 vec_to_list_length.
      destruct (lookup_lt_is_Some_2 l2 i) as [y Hy]; first by rewrite -Hl2 vec_to_list_length.
      rewrite Hx Hy /=.
      rewrite -(fin_to_nat_to_fin _ _ Hlt) -Hl1 in Hx.
      rewrite -(fin_to_nat_to_fin _ _ Hlt) -Hl2 in Hy.
      apply vlookup_lookup in Hx.
      apply vlookup_lookup in Hy.
      rewrite -(fin_to_nat_to_fin _ _ Hlt).
      symmetry; apply vlookup_lookup.
      rewrite vc_mrge_lookup Hx Hy; done.
    - rewrite !lookup_ge_None_2; rewrite -?Hl1 -?Hl2 ?vec_to_list_length; auto with lia.
  Qed.

  Lemma vector_clock_to_val_inj l1 l2 : vector_clock_to_val l1 = vector_clock_to_val l2 → l1 = l2.
  Proof.
    revert l2; induction l1 as [|a l1 IHl1]; intros l2.
    - destruct l2; inversion 1; done.
    - destruct l2; first by inversion 1.
      inversion 1; simplify_eq.
      erewrite IHl1; done.
  Qed.

  Lemma wp_gcounter_merge ip v1 v2 vc1 vc2 :
    {{{ ⌜length vc1 = length vc2⌝ ∗ ⌜is_vc v1 vc1⌝ ∗ ⌜is_vc v2 vc2⌝ }}}
      gcounter_merge v1 v2 @[ip]
    {{{w, RET w; ⌜is_vc w (vector_clock_merge vc1 vc2)⌝}}}.
  Proof.
    iIntros (Φ) "(%Hlen & %Hv1 & %Hv2) HΦ".
    rewrite /gcounter_merge.
    iInduction vc1 as [|a vc1] "IH" forall (Φ v1 v2 vc2 Hlen Hv1 Hv2).
    { destruct vc2; last done. rewrite Hv1 Hv2. wp_pures.
      iApply "HΦ"; done. }
    destruct vc2 as [|b vc2]; first done.
    simpl in *.
    destruct Hv1 as [v1' [-> ?]].
    destruct Hv2 as [v2' [-> ?]].
    wp_pures.
    destruct (decide (a ≤ b)).
    - rewrite bool_decide_eq_true_2; last lia.
      wp_if; wp_let.
      wp_apply ("IH" $! _ v1' v2' vc2 with "[] [] []"); [iPureIntro; lia|done|done|].
      iIntros (w) "%Hw".
      wp_pures.
      replace #b with $ #b; last done.
      rewrite /is_vc in Hw.
      wp_apply (wp_list_cons _ (vector_clock_merge vc1 vc2) with "[]"); first done.
      iIntros (w') "%". iApply "HΦ".
      rewrite Nat.max_r; done.
    - rewrite bool_decide_eq_false_2; last lia.
      wp_if; wp_let.
      wp_apply ("IH" $! _ v1' v2' vc2 with "[] [] []"); [iPureIntro; lia|done|done|].
      iIntros (w) "%Hw".
      wp_pures.
      replace #a with $ #a; last done.
      rewrite /is_vc in Hw.
      wp_apply (wp_list_cons _ (vector_clock_merge vc1 vc2) with "[]"); first done.
      iIntros (w') "%". iApply "HΦ".
      rewrite Nat.max_l; last lia; done.
  Qed.

  Lemma wp_perform_merge l (vcx : vector_clock (GClen gcdata)) vc i (j : fin (GClen gcdata)) a :
    gcd_addr_list gcdata !! i = Some a →
    vc = vec_to_list vcx →
    {{{ GCallocated i l ∗ GCounterSnapShot j vcx ∗ Global_Inv }}}
      perform_merge #l (vector_clock_to_val vc) @[ip_of_address a]
    {{{ RET #(); GCounterSnapShot i vcx }}}.
  Proof.
    iIntros (Hia Hvcvcx Φ) "#(Hial & Hsnap & Hinv) HΦ".
    assert (length vc = GClen gcdata) as Hvclen.
    { rewrite Hvcvcx vec_to_list_length //. }
    rewrite /perform_merge.
    iLöb as "IH".
    wp_pures.
    wp_bind (! _)%E.
    iInv CvRDT_InvName as (st locs sevss revss)
      "(Hfst & HGC & >Hlocs & Hsevss & >Hrevss & >Hlocs_coh & Hsevss_coh & Hrevss_coh & Hnet)"
      "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil.
    iDestruct "Hl" as (vc' Hfivc') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc'; simplify_eq Hfivc'; intros <-.
    wp_load.
    iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
    { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame.
      rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
      iFrame. }
    iModIntro.
    wp_pures.
    wp_apply wp_gcounter_merge.
    { iSplit; last by eauto using vector_clock_to_val_is_vc.
      rewrite vec_to_list_length Hvclen; done. }
    iIntros (w Hw).
    wp_bind (CAS _ _ _).
    iInv CvRDT_InvName as (st' locs' sevss' revss')
      "(>Hfst & >HGC & >Hlocs & Hsevss & Hrevss & >Hlocs_coh & Hsevss_coh & Hrevss_coh & Hnet)"
      "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil'.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil'.
    iDestruct "Hl" as (vc' Hfivc'') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc''; simplify_eq Hfivc''; intros <-.
    destruct (decide (st !!! fi = st' !!! fi)) as [Heq|Hneq].
    - iDestruct (GCounterSnapShot_le j with "Hsnap HGC") as %Hmrel.
      iApply aneris_wp_atomic_take_step_model.
      iModIntro.
      iExists _, _; iFrame "Hfst".
      iSplit.
      { iPureIntro; right.
        eapply (ApplyStep _ _ fi j); apply Hmrel. }
      wp_cas_suc; first by rewrite Heq.
      iIntros "Hfst".
      assert (length (vector_clock_merge (vec_to_list (st !!! fi)) vc) = GClen gcdata) as Hnewlen.
      { apply vector_clock_merge_length; first rewrite vec_to_list_length; done. }
      iMod (GCounters_update fi (vc_merge (st' !!! fi) vcx) with "HGC") as "[HGC _]";
        first by apply vc_merge_le1.
      iDestruct ("Hback" $! (Some l) (vc_merge (st' !!! fi) vcx) with "[Hevs Hl]") as "Hlocs_coh".
      { erewrite <- (is_vc_vector_clock_to_val w); last by eauto.
        erewrite vector_clock_merge_vc_merge; eauto.
        iExists _; iSplit; first by rewrite fin_to_nat_to_fin.
        rewrite Heq. iFrame. }
      iMod (get_GCounterSnapShot_weaken fi _ vcx with "HGC") as "[HGC #Hvcsnap]".
      { rewrite vlookup_insert. apply vc_merge_le2. }
      iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
      { iNext; iExists _, _, _, _; iFrame.
        rewrite list_insert_id; last by rewrite fin_to_nat_to_fin.
        iFrame. }
      iApply fupd_mask_intro_subseteq; first done.
      wp_if.
      rewrite fin_to_nat_to_fin.
      iApply "HΦ"; done.
    - wp_cas_fail.
      { intros Heq'%vector_clock_to_val_inj; apply Hneq.
        apply vec_to_list_inj2; done. }
      iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
      { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
      iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
      { iNext; iExists _, _, _, _; iFrame.
        rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
        iFrame. }
      iModIntro.
      wp_if.
      iApply "IH"; done.
  Qed.

  Lemma gcounter_apply_proof l sh i a :
    gcd_addr_list gcdata !! i = Some a →
    {{{ ([∗ list] a ∈ gcd_addr_list gcdata, a ⤇ GCounter_socket_proto) ∗
        GCallocated i l ∗ Global_Inv ∗ recevs_frag i [] ∗
        inv (nroot .@ "skt") (sh ↪[ip_of_address a] mkSocket (Some a) true) }}}
      gcounter_apply #l #(LitSocket sh) @[ip_of_address a]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hia Φ) "(#Hprotos & #Hial & #Hinv & Hrevsfrg & #Hsh) _".
    rewrite /gcounter_apply.
    do 6 wp_pure _.
    iAssert ([∗ list] rev ∈ (@nil (vector_clock (GClen gcdata))), GCounterSnapShot i rev)%I
      as "Hsnaps".
    { done. }
    generalize (@nil (vector_clock (GClen gcdata))); intros revs.
    iLöb as "IH" forall (revs) "Hsnaps".
    wp_pures.
    wp_bind (ReceiveFrom _).
    iInv CvRDT_InvName as (st locs sevss revss)
      "(Hfst & HGC & Hlocs & Hsevss & >Hrevss & Hlocs_coh & Hsevss_coh & >Hrevss_coh & >Hnet)"
      "Hcl".
    iDestruct (big_sepL_lookup_acc with "Hnet") as "[Hnet Hback]"; first by apply Hia.
    iDestruct "Hnet" as (R T) "[Ha #HR]".
    iDestruct (big_sepL_lookup with "Hprotos") as "Hproto"; first by apply Hia.
    iInv (nroot .@ "skt") as "Hsh'" "Hshcl".
    iDestruct (recevs_agree with "Hrevss Hrevsfrg") as %Hlu.
    iDestruct (recevs_coherence_insert_acc with "Hrevss_coh") as "[Hrevs Hback']"; first apply Hlu.
    iDestruct "Hrevs" as (sa' prevs Hsa') "(_ & Halloc & Hprevs & %Hrevs_cor)".
    rewrite Hia in Hsa'; simplify_eq Hsa'; intros <-.
    wp_apply (aneris_wp_receivefrom_tracked _ _ _ _ _ _ _ _ _ _ (λ _, True)%I (λ _, True)%I
                with "[$Hsh' $Hprevs $Ha $Hproto]");
      [done|done|done| |].
    { iSplitL; last iNext; auto. }
    iIntros (m) "(% & H & Hprevs)".
    iDestruct "Hprevs" as (σ stks r ?) "(Hprevs & _ & _)".
    iAssert (sh ↪[ ip_of_address a] mkSocket (Some a) true ∗
             GCounter_socket_proto m ∗
             ∃ R T, a ⤳[true, true] (R, T) ∗ ([∗ set] m ∈ R, GCounter_socket_proto m))%I
      with "[H HR]" as "(Hsh' & #Hm & Hnet)".
    { iDestruct "H" as "[(% & $ & Ha & _ & #Hm)|(%HmR & $ & Ha)]".
      - iFrame "#". iExists _, _; iFrame "Ha".
        rewrite big_sepS_insert //; iFrame "#".
      - iDestruct (big_sepS_elem_of with "HR") as "Hm"; first by apply HmR.
        iFrame "#". iExists _, _; iFrame "Ha"; done. }
    iDestruct ("Hback" with "Hnet") as "Hnet".
    iMod ("Hshcl" with "Hsh'") as "_".
    iDestruct "Hm" as (vc k j Hvc Hkm Hjm Hkj Hvclen) "Hmsnap".
    iDestruct ("Hback'" $! (revs ++ [vc]) with "[Hprevs]") as "Hrevss_coh".
    { iExists _, _; iSplit; first done. iFrame.
      iSplit.
      - iIntros (rev n Hn Hnlu).
        assert (n < length revs + 1).
        { apply lookup_lt_Some in Hnlu. rewrite app_length in Hnlu; done. }
        rewrite app_length /= in Hn.
        assert (n < length revs) by lia.
        rewrite lookup_app_l in Hnlu; last done.
        iDestruct (big_sepL_lookup _ _ n with "Hsnaps") as "?"; done.
      - iSplit; first by eauto.
        iPureIntro. apply Forall2_app; first done.
        apply List.Forall2_cons; last done.
        eexists _, _, _, _, _, _; eauto. }
    iMod (recevs_update _ _ _ (revs ++ [vc]) with "Hrevss Hrevsfrg") as "[Hrevss Hrevsfrg]".
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame. }
    iApply fupd_mask_intro_subseteq; first done.
    wp_apply wp_unSOME; first done.
    iIntros "_".
    wp_pures.
    wp_apply wp_vect_deserialize; first done.
    iIntros "_".
    wp_pures.
    assert (k < GClen gcdata) as Hklt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fk := nat_to_fin Hklt).
    wp_apply (wp_perform_merge _ vc vc i fk); [done|done|by rewrite fin_to_nat_to_fin; iFrame "#"|].
    iIntros "#Hvcsnap".
    do 2 wp_pure _.
    wp_apply ("IH" with "Hrevsfrg").
    iModIntro.
    rewrite big_sepL_snoc; iFrame "#".
  Qed.

  Lemma wp_sendToAll (i : fin (GClen gcdata)) (vc : vector_clock (GClen gcdata)) l sevs a sh v s :
    gcd_addr_list gcdata !! (fin_to_nat i) = Some a →
    is_list (gcd_addr_list gcdata) v →
    vc_is_ser (vector_clock_to_val vc) s →
    (∀ sev, sev ∈ sevs → vc_le sev.2.1 vc) →
    {{{ GCounterSnapShot i vc ∗
        inv (nroot.@"skt") (sh ↪[ ip_of_address a] mkSocket (Some a) true) ∗
        Global_Inv ∗ sendevs_frag i sevs ∗ GCallocated i l ∗
        [∗ list] a0 ∈ gcd_addr_list gcdata, a0 ⤇ GCounter_socket_proto }}}
      sendToAll #(LitSocket sh) #s v #i @[ip_of_address a]
    {{{ sevs', RET #(); sendevs_frag i sevs' }}}.
  Proof.
    iIntros (Hia Hv Hvcs Hvc_valid Φ) "(#Hsnap & #Hsh & #Hinv & Hsevsfrg & #Hial & #Hprotos) HΦ".
    assert (length vc = GClen gcdata) as Hvclen.
    { rewrite vec_to_list_length //. }
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    rewrite /sendToAll.
    do 10 wp_pure _.
    change 0%Z with (0%nat : Z).
    rewrite -(app_nil_r sevs).
    assert (∀ sev, sev ∈ @nil (nat * (vector_clock (GClen gcdata) * vector_clock (GClen gcdata))) →
                   sev.1 < 0) as Htl.
    { inversion 1. }
    revert Htl.
    generalize (@nil (nat * (vector_clock (GClen gcdata) * vector_clock (GClen gcdata)))).
    generalize 0%nat as z.
    intros z tl Htl.
    iLöb as "IH" forall (z tl Htl).
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (? ->).
    wp_pures.
    destruct (decide (z < GClen gcdata)%Z); last first.
    { rewrite bool_decide_eq_false_2; last done. wp_if. iApply "HΦ"; done. }
    rewrite bool_decide_eq_true_2; last done.
    wp_pures.
    destruct (decide (fin_to_nat i = z :> Z)) as [->|].
    { rewrite bool_decide_eq_true_2; last done.
      wp_if. wp_op.
      replace (z + 1)%Z with ((z + 1)%nat : Z) by lia.
      iApply ("IH" with "[] Hsevsfrg"); last done.
      iPureIntro; intros ? ?; etrans; first by apply Htl. lia. }
    rewrite bool_decide_eq_false_2; last done.
    wp_pures.
    wp_apply wp_list_nth; first done.
    iIntros (w Hw).
    destruct Hw as [[? ?]|(r & -> & Hr)]; first lia.
    apply misc.nth_error_lookup in Hr.
    wp_apply wp_unSOME; first done.
    iIntros "_".
    wp_pures.
    wp_bind (SendTo _ _ _).
    iInv CvRDT_InvName as (st locs sevss revss)
      "(Hfst & HGC & >Hlocs & >Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
      "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil.
    iDestruct (big_sepL_lookup_acc with "Hnet") as "[Hnet Hback]"; first by apply Hia.
    iDestruct "Hnet" as (R T) "[Ha #HR]".
    iDestruct (big_sepL_lookup with "Hprotos") as "Hproto"; first by apply Hr.
    iInv (nroot .@ "skt") as "Hsh'" "Hshcl".
    iDestruct (sendevs_agree with "Hsevss Hsevsfrg") as %Hsevs.
    iDestruct (sendevs_coherence_insert_acc i _ _ with "Hsevss_coh") as "[Hsevsi Hback']";
      [apply Hil|apply Hsevs|].
    iDestruct "Hsevsi" as (sa Hsa Hvl) "[Hsnaps Hrest]".
    rewrite Hia in Hsa; simplify_eq.
    iDestruct "Hrest" as (psevs) "[Hpsevs %Hpsevs]".
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback'']";
      first by rewrite fin_to_nat_to_fin; apply Hil.
    iDestruct "Hl" as (vc' Hfivc'') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc''; simplify_eq Hfivc''; intros <-.
    wp_apply (aneris_wp_send_tracked
                _ _ _ _ _ _ _ _ _ _ _ psevs
                (λ σ,
                   l ↦[ip_of_address sa] vector_clock_to_val (vec_to_list (st !!! fi)) ∗
                   ∃ h : heap, ⌜σ.(state_heaps) !! (ip_of_address sa) = Some h ∧
                        h !! l = Some (vector_clock_to_val (vec_to_list (st !!! fi)))⌝)%I
                (λ σ, True)%I
                with "[$Hsh' $Ha $Hproto $Hpsevs Hl]"); [done|done| |].
    { iSplitR.
      { iNext. iExists _, _, _; repeat iSplit; eauto. }
      iSplitL; last by eauto.
      iIntros (σ δ) "Hsi".
      iDestruct (aneris_state_interp_heap_valid with "Hsi Hl") as (h) "[% %]".
      iModIntro; iFrame; eauto. }
    iIntros "(Hsh' & Ha & Hev)".
    iDestruct "Hev" as (σ skts r' Hr') "(Hpsevs & [Hl Hh] & _)".
    iDestruct "Hh" as (h) "[% %]".
    iDestruct ("Hback''" $! (Some l) with "[Hl Hevs]") as "Hlocs_coh".
    { iExists _; iSplit; first by rewrite fin_to_nat_to_fin. iFrame. }
    iMod (get_GCounterSnapShot fi with "HGC") as "[HGC #Hsnap']".
    iMod (sendevs_update _ _ _ (sevs ++ tl ++ [(z, ((st !!! fi), vc))]) with "Hsevss Hsevsfrg")
      as "[Hsevss Hsevsfrg]".
    iDestruct ("Hback'" $! (Some l) (sevs ++ tl ++ [(z, (st !!! fi, vc))]) with "[Hsnaps Hpsevs]")
      as "Hsevss_coh".
    { iExists _; iSplit; first done.
      iSplit.
      { iPureIntro. apply sendevs_valid_extend; [done| |done].
        intros sev Hsev; simpl.
        apply Htl in Hsev; lia. }
      iSplit.
      { rewrite assoc_L big_sepL_snoc fin_to_nat_to_fin; auto. }
      iExists _; iFrame.
      iPureIntro.
      rewrite assoc_L.
      apply Forall2_app; first done.
      apply List.Forall2_cons; last done.
      eexists _, _, _, _, _, _, _, _; eauto 10. }
    iDestruct ("Hback" with "[Ha]") as "Hnet".
    { iExists _, _ ; iFrame; done. }
    iMod ("Hshcl" with "Hsh'") as "_".
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame.
      rewrite fin_to_nat_to_fin.
      rewrite !(list_insert_id locs) //.
      rewrite vlookup_insert_self. iFrame. }
    iApply fupd_mask_intro_subseteq; first done.
    do 2 wp_pure _.
    wp_op.
    replace (z + 1)%Z with ((z + 1)%nat : Z) by lia.
    iApply ("IH" with "[] Hsevsfrg"); [|done].
    iPureIntro.
    intros sev [| ->%elem_of_list_singleton]%elem_of_app; last by simpl; lia.
    etrans; first apply Htl; auto with lia.
  Qed.

  Lemma gcounter_broadcast_proof l sh i v a :
    gcd_addr_list gcdata !! i = Some a →
    is_list (gcd_addr_list gcdata) v →
    {{{ ([∗ list] a ∈ gcd_addr_list gcdata, a ⤇ GCounter_socket_proto) ∗
        GCallocated i l ∗ Global_Inv ∗ sendevs_frag i [] ∗
        inv (nroot .@ "skt") (sh ↪[ip_of_address a] mkSocket (Some a) true) }}}
      gcounter_broadcast #l #(LitSocket sh) v #i @[ip_of_address a]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hia Hv Φ) "(#Hprotos & #Hial & #Hinv & Hsevsfrg & #Hsh) _".
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    rewrite /gcounter_broadcast.
    do 10 wp_pure _.
    generalize (@nil (nat * (vector_clock (GClen gcdata) * vector_clock (GClen gcdata))));
      intros sevs.
    iLöb as "IH" forall (sevs).
    wp_pures.
    rewrite /sleep.
    wp_pures.
    wp_bind (! _)%E.
    iInv CvRDT_InvName as (st locs sevss revss)
      "(Hfst & HGC & >Hlocs & Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
      "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil'.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil'.
    iDestruct "Hl" as (vc' Hfivc'') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc''; simplify_eq Hfivc''; intros <-.
    wp_load; simpl.
    iMod (get_GCounterSnapShot fi with "HGC") as "[HGC #Hsnap]".
    iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
    { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
    iAssert (⌜∀ sev, sev ∈ sevs → vc_le sev.2.1 (st !!! fi)⌝)%I as %?.
    { iDestruct (sendevs_agree with "Hsevss Hsevsfrg") as %Hsevs.
      iDestruct (sendevs_coherence_insert_acc i _ _ with "Hsevss_coh") as "[Hsevsi Hback']";
      [apply Hil'|apply Hsevs|].
      iDestruct "Hsevsi" as (sa Hsa Hvl) "[Hsnaps Hrest]".
      iIntros (sev [j Hsev]%elem_of_list_lookup).
      iApply (GCounterSnapShot_le with "[Hsnaps] HGC").
      iDestruct (big_sepL_lookup _ _ j with "Hsnaps") as "?"; first by eauto.
      rewrite fin_to_nat_to_fin; done. }
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame.
      rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
      iFrame. }
    iModIntro.
    wp_pures.
    wp_apply wp_vect_serialize.
    { iPureIntro. eexists; apply vector_clock_to_val_is_vc. }
    iIntros (s Hs).
    wp_pures.
    rewrite -(fin_to_nat_to_fin _ _ Hilt).
    wp_apply (wp_sendToAll with "[$Hsevsfrg]");
      [by rewrite fin_to_nat_to_fin|done|apply Hs|done|by iFrame "#"|].
    iIntros (sevs') "Hsevs'frg".
    do 2 wp_pure _.
    iApply "IH"; done.
  Qed.

  Lemma wp_gcounter_sum ip v l :
    is_vc v l →
    {{{ True  }}} gcounter_sum v @[ip] {{{ (m : nat), RET #m; ⌜m = list_sum l⌝ }}}.
  Proof.
    iIntros (Hvl Φ) "_ HΦ".
    rewrite /gcounter_sum.
    iInduction l as [|n l IHl] "IH" forall (v Hvl Φ).
    { rewrite Hvl; wp_pures. replace #0 with #(0%nat); last done. iApply "HΦ"; done. }
    wp_pures.
    destruct Hvl as [w [-> Hw]].
    do 9 wp_pure _.
    wp_bind ((RecV _ _ _) _).
    wp_apply "IH"; first done.
    iIntros (? ->).
    wp_pures.
    replace (n + list_sum l)%Z with ((n + list_sum l)%nat : Z); last lia.
    iApply "HΦ"; done.
  Qed.

  (* definitely move *)
  Lemma list_sum_le l1 l2 : Forall2 le l1 l2 → list_sum l1 ≤ list_sum l2.
  Proof.
    revert l2; induction l1 as [|a l1 IHl1]; intros l2 Hle.
    { inversion Hle; simplify_eq; done. }
    inversion Hle; simplify_eq.
    simpl; apply Nat.add_le_mono; auto.
  Qed.

  (* definitely move *)
  Lemma vc_le_sum n (vc vc' : vector_clock n) : vc_le vc vc' → list_sum vc ≤ list_sum vc'.
  Proof.
    intros Hle.
    apply list_sum_le.
    apply Forall2_lookup; intros i.
    destruct (decide (i < n)) as [Hlt|]; last first.
    { rewrite !lookup_ge_None_2; first (by constructor); rewrite vec_to_list_length; auto with lia. }
    destruct (lookup_lt_is_Some_2 vc i) as [x Hx]; first by rewrite vec_to_list_length.
    destruct (lookup_lt_is_Some_2 vc' i) as [y Hy]; first by rewrite vec_to_list_length.
    rewrite Hx Hy; constructor.
    rewrite -(fin_to_nat_to_fin _ _ Hlt) in Hx, Hy.
    apply vlookup_lookup in Hx, Hy.
    rewrite -Hx -Hy.
    apply Hle.
  Qed.

  Lemma gcounter_query_proof l i a :
    ⊢ query_spec
      (λ i n, ∃ vc, Global_Inv ∗ GCallocated i l ∗
                 GCounterSnapShot i vc ∗ ⌜list_sum vc = n⌝)%I
      (λ: <>, gcounter_sum ! #l)%V i a.
  Proof.
    rewrite /query_spec.
    iIntros "!#" (n Hia Φ) "!# Hgc HΦ".
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    iDestruct "Hgc" as (vc) "#(Hinv & Hial & Hsnap & <-)".
    wp_pures.
    wp_bind (! _)%E.
    iInv CvRDT_InvName as (st locs sevss revss)
      "(Hfst & HGC & >Hlocs & Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
      "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil'.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil'.
    iDestruct "Hl" as (vc' Hfivc'') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc''; simplify_eq Hfivc''; intros <-.
    wp_load; simpl.
    iDestruct (GCounterSnapShot_le fi with "[Hsnap] HGC") as %?.
    { rewrite fin_to_nat_to_fin; done. }
    iMod (get_GCounterSnapShot fi with "HGC") as "[HGC #Hsnap']".
    iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
    { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame.
      rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
      iFrame. }
    iModIntro.
    wp_apply wp_gcounter_sum; [apply vector_clock_to_val_is_vc|done|].
    iIntros (m ->).
    iApply "HΦ".
    iSplit; first by iPureIntro; apply vc_le_sum.
    rewrite fin_to_nat_to_fin.
    iExists (st !!! fi); iFrame "#"; done.
  Qed.

  Lemma vec_to_list_vc_incr n (vc : vector_clock n) i :
    ∀ (H : i < n), vec_to_list (vc_incr (nat_to_fin H) vc) = incr_time vc i.
  Proof.
    intros H.
    apply list_eq; intros j.
    destruct (decide (j < n)) as [Hlt|]; last first.
    { rewrite lookup_ge_None_2; last by rewrite vec_to_list_length; lia.
      rewrite lookup_ge_None_2; last by rewrite incr_time_length vec_to_list_length; lia.
      done. }
    destruct (lookup_lt_is_Some_2 vc j) as [x Hx]; first by rewrite vec_to_list_length; lia.
    destruct (decide (i = j)) as [->|].
    - erewrite incr_time_proj; last apply Hx.
      rewrite /vc_incr.
      rewrite -{1}(fin_to_nat_to_fin _ _ H).
      apply vlookup_lookup.
      rewrite vlookup_insert.
      f_equal.
      apply vlookup_lookup; rewrite fin_to_nat_to_fin; done.
    - erewrite incr_time_proj_neq; last done.
      rewrite Hx /vc_incr.
      rewrite -(fin_to_nat_to_fin _ _ Hlt).
      apply vlookup_lookup.
      rewrite vlookup_insert_ne; last first.
      { intros Heq.
        pose proof (f_equal fin_to_nat Heq) as Heq'.
        rewrite !fin_to_nat_to_fin in Heq'; done. }
      apply vlookup_lookup.
      rewrite fin_to_nat_to_fin; done.
  Qed.

  Lemma list_sum_incr_time l i : i < length l → list_sum l < list_sum (incr_time l i).
  Proof.
    revert i; induction l as [|a l IHl]; intros i Hli; simpl in *; first lia.
    destruct i; simpl; first lia.
    apply plus_lt_compat_l; apply IHl; lia.
  Qed.

  Lemma gcounter_incr_proof l (i : nat) a :
    ⊢ incr_spec
      (λ i n, ∃ vc, Global_Inv ∗ GCallocated i l ∗ GCounterSnapShot i vc ∗ ⌜list_sum vc = n⌝)%I
      (rec: "incr" <> := let: "tmp" := ! #l in if: CAS #l "tmp" (vect_inc "tmp" #i) then
                                                 #() else "incr" #())%V
      i a.
  Proof.
    rewrite /incr_spec.
    iIntros "!#" (n Hia Φ) "!# Hgc HΦ".
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    iDestruct "Hgc" as (vc) "#(Hinv & Hial & Hsnap & <-)".
    iLöb as "IH".
    wp_pures.
    wp_bind (! _)%E.
    iInv CvRDT_InvName as (st locs sevss revss)
        "(Hfst & HGC & >Hlocs & >Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
        "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil.
    iDestruct "Hl" as (vc' Hfivc') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc'; simplify_eq Hfivc'; intros <-.
    wp_load; simpl.
    iDestruct (GCounterSnapShot_le fi with "[Hsnap] HGC") as %?.
    { rewrite fin_to_nat_to_fin; done. }
    iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
    { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
    iMod ("Hcl" with "[Hfst HGC Hsevss Hrevss Hlocs Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame.
      rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
      iFrame. }
    iModIntro.
    wp_pures.
    destruct (lookup_lt_is_Some_2 (vec_to_list (st !!! fi)) i) as [x Hx];
      first by rewrite vec_to_list_length.
    wp_apply (wp_vect_inc _ _ (vec_to_list (st !!! fi)));
      [by rewrite vec_to_list_length; lia|apply Hx|iPureIntro; apply vector_clock_to_val_is_vc|].
    iIntros (v Hv).
    erewrite <- (is_vc_vector_clock_to_val v); last apply Hv.
    wp_bind (CAS _ _ _).
    iInv CvRDT_InvName as (st' locs' sevss' revss')
        "(>Hfst & HGC & >Hlocs & Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
        "Hcl".
    iDestruct (locations_is_allocated with "Hlocs Hial") as %Hil'.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %?.
    iDestruct (locations_coherence_insert_acc fi with "Hlocs_coh") as "[Hl Hback]";
      first by rewrite fin_to_nat_to_fin; apply Hil'.
    iDestruct "Hl" as (vc' Hfivc'') "[Hevs Hl]".
    rewrite fin_to_nat_to_fin Hia in Hfivc''; simplify_eq Hfivc''; intros <-.
    destruct (decide (st !!! fi = st' !!! fi)) as [Heq|Hneq].
    - iApply aneris_wp_atomic_take_step_model.
      iModIntro.
      iExists _, _; iFrame "Hfst".
      iSplit.
      { iPureIntro; right.
        apply (IncrStep _ fi). }
      wp_cas_suc; first by rewrite Heq.
      iIntros "Hfst".
      iDestruct ("Hback" $! (Some l) (vc_incr fi (st' !!! fi)) with "[Hevs Hl]") as "Hlocs_coh".
      { iExists _; iSplit; first by rewrite fin_to_nat_to_fin.
        rewrite Heq vec_to_list_vc_incr. iFrame. }
      iMod (GCounters_update fi (vc_incr fi (st' !!! fi)) with "HGC") as "[HGC _]";
        first by apply vc_incr_le.
      iMod (get_GCounterSnapShot fi with "HGC") as "[HGC #Hsnap']".
      rewrite vlookup_insert.
      iMod ("Hcl" with "[Hfst HGC Hsevss Hrevss Hlocs Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
      { iNext; iExists _, _, _, _; iFrame.
        rewrite list_insert_id; last by rewrite fin_to_nat_to_fin.
        iFrame. }
      iApply fupd_mask_intro_subseteq; first done.
      wp_if.
      iClear "Hsnap".
      rewrite fin_to_nat_to_fin.
      iApply "HΦ".
      iExists (list_sum (vc_incr fi (st' !!! fi))); iFrame "#".
      iSplit; last by iExists _; iFrame "Hsnap'".
      iPureIntro.
      eapply le_lt_trans; first by apply vc_le_sum.
      rewrite vec_to_list_vc_incr Heq.
      apply list_sum_incr_time.
      rewrite vec_to_list_length; done.
    - wp_cas_fail.
      { intros Heq'%vector_clock_to_val_inj; apply Hneq.
        apply vec_to_list_inj2; done. }
      iDestruct ("Hback" $! (Some _) with "[Hevs Hl]") as "Hlocs_coh".
      { iExists _; iFrame; rewrite fin_to_nat_to_fin; done. }
      iMod ("Hcl" with "[Hfst HGC Hsevss Hrevss Hlocs Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
      { iNext; iExists _, _, _, _; iFrame.
        rewrite vlookup_insert_self list_insert_id; last by rewrite fin_to_nat_to_fin.
        iFrame. }
      iModIntro.
      wp_if.
      iApply "IH"; done.
    Qed.

  (* definitely move *)
  Lemma list_sum_replicate n m : list_sum (replicate n m) = n * m.
  Proof. induction n; simpl; lia. Qed.

  Lemma install_proof (i : nat) (a : socket_address) (v : val) :
    is_list (gcd_addr_list gcdata) v →
    gcd_addr_list gcdata !! i = Some a →
    {{{ Global_Inv ∗ GCunallocated i ∗
        ([∗ list] i ↦ a ∈ gcd_addr_list gcdata, a ⤇ GCounter_socket_proto) ∗
        unbound {[a]} ∗
        sendevs_frag i [] ∗ recevs_frag i [] }}}
      gcounter_install (StringOfZ i) v #i @[ip_of_address a]
    {{{ (GCounter : nat → nat → iProp Σ) query incr, RET (query, incr);
        GCounter i 0 ∗ query_spec GCounter query i a ∗ incr_spec GCounter incr i a}}}.
  Proof.
    iIntros (Hilv Hia Φ) "(#Hgi & Hua & #Hprotos & Hfpa & Hsevsfrg & Hrevsfrg) HΦ".
    rewrite /gcounter_install.
    assert (i < GClen gcdata) as Hilt.
    { apply lookup_lt_is_Some_1; eauto. }
    set (fi := nat_to_fin Hilt).
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (? ->).
    wp_pures.
    replace #0 with #0%nat; last done.
    wp_apply wp_vect_make; first done.
    iIntros (w Hw).
    wp_bind (ref<<_>> _)%E.
    iInv CvRDT_InvName as (st locs sevss revss)
        "(Hfst & HGC & >Hlocs & >Hsevss & Hrevss & >Hlocs_coh & >Hsevss_coh & Hrevss_coh & Hnet)"
        "Hcl".
    iDestruct (locations_is_unallocated with "Hlocs Hua") as %Hlocsi.
    iDestruct (locations_coherence_length with "Hlocs_coh") as %Hlocslen.
    iDestruct (locations_coherence_insert_acc fi _ None with "Hlocs_coh") as "[Hloci Hback]".
    { by rewrite fin_to_nat_to_fin. }
    iDestruct (sendevs_coherence_length with "Hsevss_coh") as %Hsevsslen.
    destruct (lookup_lt_is_Some_2 sevss i) as [sevs Hsevs]; first by rewrite -Hsevsslen Hlocslen.
    iDestruct (sendevs_coherence_insert_acc i _ None with "Hsevss_coh") as "[Hsevsi Hback']";
      [apply Hlocsi|apply Hsevs|].
    iDestruct "Hloci" as "[Hlocievs %Hstfi]".
    wp_apply (aneris_wp_alloc_tracked with "[Hlocievs]");
      first by rewrite (fin_to_nat_to_fin _ _ Hilt).
    iIntros (l h σ) "(Hl & % & Hlocievs)".
    iPoseProof ("Hback" $! (Some l) (vreplicate (GClen gcdata) 0) with "[Hl Hlocievs]") as "Hlocs_coh".
    { iExists _; iSplit; rewrite (fin_to_nat_to_fin _ _ Hilt); first done.
      erewrite is_vc_vector_clock_to_val; last by rewrite vec_to_list_replicate.
      iFrame. iExists _, _; iFrame; done. }
    rewrite -Hstfi vlookup_insert_self.
    iPoseProof ("Hback'" $! (Some l) sevs with "[Hsevsi]") as "Hsevss_coh".
    { iDestruct "Hsevsi" as (sa' Hsa' ?) "(? & ? & ->)".
      rewrite Hia in Hsa'; simplify_eq Hsa'; intros <-.
      iExists _; iSplit; first done.
      iSplit; first done.
      iFrame.
      iExists _; iFrame; auto. }
    rewrite (list_insert_id sevss); last done.
    iMod (locations_alloc with "Hlocs Hua") as "[Hlocs #Hial]".
    iMod (get_GCounterSnapShot fi with "HGC") as "[HGC #Hsnap]".
    rewrite !fin_to_nat_to_fin Hstfi.
    iMod ("Hcl" with "[Hfst HGC Hlocs Hsevss Hrevss Hlocs_coh Hsevss_coh Hrevss_coh Hnet]") as "_".
    { iNext; iExists _, _, _, _; iFrame. }
    iModIntro.
    wp_pures.
    wp_apply wp_list_nth; first done.
    iIntros (? [[]| (r & -> & Hr)]); first lia.
    apply misc.nth_error_lookup in Hr.
    rewrite Hia in Hr; simplify_eq.
    wp_apply wp_unSOME; first done.
    iIntros "_".
    wp_pures.
    wp_socket sh as "Hsh".
    wp_pures.
    wp_socketbind.
    iMod (inv_alloc (nroot .@ "skt") _ (sh ↪[ ip_of_address r] mkSocket (Some r) true)
            with "[$Hsh //]") as "#Hsh".
    wp_apply aneris_wp_fork.
    iSplitR "Hrevsfrg"; last first.
    { iNext. iApply (gcounter_apply_proof with "[Hrevsfrg]"); eauto. }
    iNext.
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitR "Hsevsfrg"; last first.
    { iNext. iApply (gcounter_broadcast_proof with "[Hsevsfrg]"); eauto. }
    iNext.
    wp_pures.
    rewrite /gcounter_query /gcounter_incr /=.
    wp_pures.
    iApply ("HΦ" $! (λ i n, ∃ vc, Global_Inv ∗ GCallocated i l ∗
                                GCounterSnapShot i vc ∗ ⌜list_sum vc = n⌝)%I).
    iSplit.
    { iExists _; iFrame "#". rewrite vec_to_list_replicate list_sum_replicate; auto with lia. }
    iSplit.
    - iApply gcounter_query_proof.
    - iApply gcounter_incr_proof.
  Qed.

End proof.

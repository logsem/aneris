From stdpp Require Import base gmap.
From aneris.aneris_lang.lib Require Import list_proof.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang Require Import adequacy.
From aneris.aneris_lang.program_logic Require Import aneris_adequacy.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
     Require Import semi_join_lattices model params.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.proof
     Require Import events spec stlib_proof_setup stlib_proof_utils internal_specs stlib_proof.
From aneris.examples.crdt.statelib.examples.gcounter
     Require Import gcounter_proof.
From aneris.examples.crdt.statelib.examples.prod_comb
     Require Import prod_comb_proof.
From aneris.examples.crdt.statelib.examples.pncounter
     Require Import pncounter_code_wrapper pncounter_proof.

Definition addresses := [SocketAddressInet "1.1.1.1" 100; SocketAddressInet "1.1.1.2" 100].
Definition addresses_val : val := $ [SocketAddressInet "1.1.1.1" 100; SocketAddressInet "1.1.1.2" 100].


Program Instance pnc_use_case_CRDT_Params : CRDT_Params :=
  {| CRDT_Addresses := addresses;
    CRDT_InvName := nroot .@ "gi_pnuc"|}.
Next Obligation.
Proof. repeat constructor; set_solver. Defined.

Definition use_case_program1 : expr :=
  let: "init_res" := pncounter_init addresses_val #0%nat in
  let: "get" := Fst "init_res" in
  let: "update" := Snd "init_res" in
  "update" #1;;
  let: "r" := "get" #() in
  assert: ("r" = #1) || ("r" = #3).

Definition use_case_program2 : expr :=
  let: "init_res" := pncounter_init addresses_val #1%nat in
  let: "get" := Fst "init_res" in
  let: "update" := Snd "init_res" in
  "update" #2;;
  let: "r" := "get" #() in
  assert: ("r" = #2) || ("r" = #3).

Definition use_case_program : expr :=
  Start "1.1.1.1" use_case_program1;;
  Start "1.1.1.2" use_case_program2.

(* TODO: move this more usefule version of the lemma to its approporate place. *)
Lemma LocSnap_GlobSnap_Provenance' `{!anerisG Mdl Σ} `{!CRDT_Params} `{!Log_Time}
    `{!EqDecision CRDT_Op} `{!Countable CRDT_Op} `{!crdt_resources.CRDT_Res_Mixin Mdl Σ CRDT_Op}
    E i s1 s2 h:
  ↑CRDT_InvName ⊆ E → GlobInv -∗ GlobSnap h -∗ LocSnap i s1 s2 ={E}=∗
  ∃ h' : event_set CRDT_Op, GlobSnap h' ∗ ⌜s1 ∪ s2 ⊆ h'⌝ ∗ ⌜h ⊆ h'⌝.
Proof.
  iIntros (?) "#Hinv #HGsnap #HLsnap".
  set (s := s1 ∪ s2).
  assert (s ⊆ s1 ∪ s2) as Hs by set_solver.
  clearbody s.
  iInduction s as [|ev h'] "IH" using set_ind_L forall (s1 s2 Hs) "HLsnap".
  - iModIntro. iExists _; iFrame "#"; iSplit; iPureIntro; set_solver.
  - iMod ("IH" with "[] HLsnap") as (h'') "(HGsnap' & % & %)"; first by iPureIntro; set_solver.
    iMod (LocSnap_GlobSnap_Provenance _ _ _ _ ev with "[//] HLsnap") as (h3) "[HGsnap3 %]";
      [set_solver|set_solver|].
    iModIntro.
    iDestruct (GlobSnap_Union with "HGsnap' HGsnap3") as "HGsnap'".
    iExists (h'' ∪ h3); iFrame.
    iPureIntro; split; set_solver.
Qed.

Section use_case_proof.
  Context `{!anerisG M Σ} `{!inG Σ (exclR unitO)}.
  (* Context `{stparams0 : !StLib_Res (prodOp gctr_op gctr_op)}. *)
  Context `{!StLib_Res CtrOp}.
  Definition use_case_inv_name := nroot .@ "pnuc".

  Definition use_case_inv `{!StLib_Res CtrOp} γ1 γ2 : iProp Σ :=
    ∃ ges, GlobState ges ∗
      (⌜ges = ∅⌝ ∨
       (∃ ev, ⌜ges = {[ev]} ∧ EV_Op ev = Add 1 ∧ EV_Orig ev = 0%nat⌝ ∗ own γ1 (Excl ())) ∨
       (∃ ev, ⌜ges = {[ev]} ∧ EV_Op ev = Add 2 ∧ EV_Orig ev = 1%nat⌝ ∗ own γ2 (Excl ())) ∨
       (∃ ev1 ev2, ⌜ges = {[ev1; ev2]} ∧
          EV_Op ev1 = Add 1 ∧ EV_Orig ev1 = 0%nat ∧
          EV_Op ev2 = Add 2 ∧ EV_Orig ev2 = 1%nat⌝ ∗
          own γ1 (Excl ()) ∗ own γ2 (Excl ()))).

  Program Definition Ofin : fin (length CRDT_Addresses).
  Proof. apply (@Fin.of_nat_lt 0 (length addresses)); simpl; lia.  Defined.

  Lemma wp_use_case_program1  γ1 γ2 :
    {{{ GlobInv ∗ StLib_InitToken Ofin ∗ pn_init_crdt_spec pncounter_init ∗
        ([∗ list] i↦z ∈ CRDT_Addresses, z ⤇ StLib_SocketProto) ∗
        SocketAddressInet "1.1.1.1" 100 ⤳ (∅, ∅) ∗ free_ports "1.1.1.1" {[100%positive]} ∗
        inv use_case_inv_name (use_case_inv γ1 γ2) ∗ own γ1 (Excl ()) }}}
      use_case_program1 @["1.1.1.1"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ)
      "(#HGinv & Hcrdt_tk & Hinit & #Hprotos & Hsa & Hfp & #Hinv & Htok) HΦ".
    rewrite /use_case_program1.
    wp_apply ("Hinit" $! _ (SocketAddressInet "1.1.1.1" 100) addresses_val
               with "[$Hsa $Hfp $Hcrdt_tk]").
    { iFrame "#".
      iSplit; first by iPureIntro; apply is_list_inject.
      iPureIntro; set_solver. }
    iIntros (get upd) "(Hls & #Hget & #Hupd)".
    wp_pures.
    wp_apply ("Hupd" $! _ (Add _)); [done|done|].
    iInv use_case_inv_name as (ges) ">[HGs Hstate]" "Hclose".
    iMod fupd_mask_subseteq as "Hmask"; [|iModIntro]; [solve_ndisj|].
    iExists _, _, _; iFrame.
    iNext.
    iIntros (add_1_ev h' s1' s2').
    rewrite !left_id_L.
    iIntros "(%Hadd_1_val & %Hadd_1_orig & -> & -> & % & % & % & % & % & HGs & HLs)".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[HGs Hstate Htok]") as "_".
    { iNext.
      iDestruct "Hstate" as "[->|[Hstate|[Hstate|Hstate]]]".
      - iExists {[add_1_ev]}.
        rewrite left_id_L.
        iFrame "HGs"; eauto.
      - iDestruct "Hstate" as (?) "[? Htok']".
        iDestruct (own_valid_2 with "Htok Htok'") as %?; done.
      - iDestruct "Hstate" as (?) "[(%&%&%) Htok']"; simplify_eq.
        iExists _; iFrame "HGs".
        iRight; iRight; iRight.
        iExists add_1_ev, ev; iFrame.
        iPureIntro.
        split_and!; [set_solver|done|done|done|done].
      - iDestruct "Hstate" as (? ?) "(? & Htok' & ?)".
        iDestruct (own_valid_2 with "Htok Htok'") as %?; done. }
    iModIntro.
    wp_pures.
    wp_apply "Hget"; first done.
    iMod fupd_mask_subseteq as "Hmask"; [|iModIntro]; [solve_ndisj|].
    iExists _, _; iFrame "HLs".
    iNext.
    iIntros (s3 pst lst) "(% & HLs & %Hop & %Hst)".
    iMod "Hmask" as "_".
    iInv use_case_inv_name as (ges') ">[HGs Hstate]" "Hclose".
    iDestruct (LocState_TakeSnap with "HLs") as "[HLs HLsnap]".
    assert (↑CRDT_InvName ⊆ ⊤ ∖ ↑use_case_inv_name) by solve_ndisj.
    iMod (GlobState_TakeSnap with "[//] HGs") as "[HGs HGsnap]"; first done.
    iMod (LocSnap_GlobSnap_Provenance' with "[//] HGsnap HLsnap") as (h) "(#HGsnap & % & %)";
      first done.
    iMod (GlobSnap_GlobState_Included with "[//] HGsnap HGs") as "[% HGs]"; first done.
    assert (h = ges') as -> by set_solver.
    iDestruct "Hstate" as "[->|[Hstate|[Hstate|Hstate]]]".
    - set_solver.
    - iDestruct "Hstate" as (ev) "[(%&%Hev_val&%) Htk]"; simplify_eq.
      assert (add_1_ev = ev) as <- by set_solver.
      assert ({[add_1_ev]} ∪ s3 = {[add_1_ev]}) as Hunion_eq by set_solver.
      rewrite Hunion_eq in Hst.
      rewrite /crdt_denot /= /ctr_denot elements_singleton /= /ctr_payload Hev_val in Hst; subst.
      rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
      iMod ("Hclose" with "[HGs Htk]") as "_".
      { iNext. iExists _; iFrame "HGs"; eauto. }
      iModIntro.
      do 2 wp_pure _.
      wp_apply assert_proof.wp_assert.
      wp_pures. iSplit; first done.
      iNext; iApply "HΦ"; done.
    - iDestruct "Hstate" as (ev) "[(%&%Hev_val&%) Htk]"; simplify_eq.
      assert (add_1_ev = ev) as <- by set_solver.
      iDestruct (LocState_OwnOrig with "HLs") as %Horigs.
      assert (EV_Orig add_1_ev = 0%nat); last congruence.
      apply Horigs; set_solver.
    - iDestruct "Hstate" as (ev1 ev2) "[(%&%Hev1_val&%&%Hev2_val&%) [Htk1 Htk2]]"; simplify_eq.
      iDestruct (LocState_OwnOrig with "HLs") as %Horigs.
      assert (EV_Orig add_1_ev = 0%nat).
      { apply Horigs; set_solver. }
      assert (add_1_ev = ev1 ∨ add_1_ev = ev2) as [|] by set_solver; [subst|congruence].
      assert ({[ev1]} ∪ s3 = {[ev1]} ∨ {[ev1]} ∪ s3 = {[ev1; ev2]}) as Hunion_eq.
      { destruct (decide (ev2 ∈ s3)).
        - right; set_solver.
        - left; set_solver. }
      destruct Hunion_eq as [Hunion_eq|Hunion_eq].
      + rewrite Hunion_eq in Hst.
        rewrite /crdt_denot /= /ctr_denot elements_singleton /= /ctr_payload Hev1_val in Hst; subst.
        rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
        iMod ("Hclose" with "[HGs Htk1 Htk2]") as "_".
        { iNext. iExists _; iFrame "HGs"; iRight; iRight; iRight; iExists _, _; iFrame; eauto. }
        iModIntro.
        do 2 wp_pure _.
        wp_apply assert_proof.wp_assert.
        wp_pures. iSplit; first done.
        iNext; iApply "HΦ"; done.
      + assert (ev1 ≠ ev2) by congruence.
        rewrite Hunion_eq in Hst.
        rewrite /crdt_denot /= /ctr_denot in Hst.
        erewrite ctr_value_perm in Hst; last by apply elements_disj_union; set_solver.
        rewrite !elements_singleton /= /ctr_payload Hev1_val Hev2_val in Hst.
        rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
        iMod ("Hclose" with "[HGs Htk1 Htk2]") as "_".
        { iNext. iExists _; iFrame "HGs"; iRight; iRight; iRight; iExists _, _; iFrame; eauto. }
        iModIntro.
        do 2 wp_pure _.
        wp_apply assert_proof.wp_assert.
        wp_pures. iSplit; first done.
        iNext; iApply "HΦ"; done.
  Qed.

  Program Definition Ifin : fin (length CRDT_Addresses).
  Proof. apply (@Fin.of_nat_lt 1 (length addresses)); simpl; lia. Defined.

  Lemma wp_use_case_program2 `{!StLib_Res CtrOp} γ1 γ2 :
    {{{ GlobInv ∗ StLib_InitToken Ifin ∗ pn_init_crdt_spec pncounter_init ∗
        ([∗ list] i↦z ∈ CRDT_Addresses, z ⤇ StLib_SocketProto) ∗
        SocketAddressInet "1.1.1.2" 100 ⤳ (∅, ∅) ∗ free_ports "1.1.1.2" {[100%positive]} ∗
        inv use_case_inv_name (use_case_inv γ1 γ2) ∗ own γ2 (Excl ()) }}}
      use_case_program2 @["1.1.1.2"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ)
      "(#HGinv & Hcrdt_tk & Hinit& #Hprotos & Hsa & Hfp & #Hinv & Htok) HΦ".
    rewrite /use_case_program2.
    wp_apply ("Hinit" $! _ (SocketAddressInet "1.1.1.2" 100) addresses_val
               with "[$Hsa $Hfp $Hcrdt_tk]").
    { iFrame "#".
      iSplit; first by iPureIntro; apply is_list_inject.
      iPureIntro; set_solver. }
    iIntros (get upd) "(Hls & #Hget & #Hupd)".
    wp_pures.
    wp_apply ("Hupd" $! _ (Add _)); [done|done|].
    iInv use_case_inv_name as (ges) ">[HGs Hstate]" "Hclose".
    iMod fupd_mask_subseteq as "Hmask"; [|iModIntro]; [solve_ndisj|].
    iExists _, _, _; iFrame.
    iNext.
    iIntros (add_2_ev h' s1' s2').
    rewrite !left_id_L.
    iIntros "(%Hadd_2_val & %Hadd_2_orig & -> & -> & % & % & % & % & % & HGs & HLs)".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[HGs Hstate Htok]") as "_".
    { iNext.
      iDestruct "Hstate" as "[->|[Hstate|[Hstate|Hstate]]]".
      - iExists {[add_2_ev]}.
        rewrite left_id_L.
        iFrame "HGs"; eauto 10.
      - iDestruct "Hstate" as (?) "[(%&%&%) Htok']"; simplify_eq.
        iExists _; iFrame "HGs".
        iRight; iRight; iRight.
        iExists ev, add_2_ev; iFrame.
        iPureIntro.
        split_and!; [set_solver|done|done|done|done].
      - iDestruct "Hstate" as (?) "[? Htok']".
        iDestruct (own_valid_2 with "Htok Htok'") as %?; done.
      - iDestruct "Hstate" as (? ?) "(? & ? & Htok')".
        iDestruct (own_valid_2 with "Htok Htok'") as %?; done. }
    iModIntro.
    wp_pures.
    wp_apply "Hget"; first done.
    iMod fupd_mask_subseteq as "Hmask"; [|iModIntro]; [solve_ndisj|].
    iExists _, _; iFrame "HLs".
    iNext.
    iIntros (s3 pst lst) "(% & HLs & %Hop & %Hst)".
    iMod "Hmask" as "_".
    iInv use_case_inv_name as (ges') ">[HGs Hstate]" "Hclose".
    iDestruct (LocState_TakeSnap with "HLs") as "[HLs HLsnap]".
    assert (↑CRDT_InvName ⊆ ⊤ ∖ ↑use_case_inv_name) by solve_ndisj.
    iMod (GlobState_TakeSnap with "[//] HGs") as "[HGs HGsnap]"; first done.
    iMod (LocSnap_GlobSnap_Provenance' with "[//] HGsnap HLsnap") as (h) "(#HGsnap & % & %)";
      first done.
    iMod (GlobSnap_GlobState_Included with "[//] HGsnap HGs") as "[% HGs]"; first done.
    assert (h = ges') as -> by set_solver.
    iDestruct "Hstate" as "[->|[Hstate|[Hstate|Hstate]]]".
    - set_solver.
    - iDestruct "Hstate" as (ev) "[(%&%Hev_val&%) Htk]"; simplify_eq.
      assert (add_2_ev = ev) as <- by set_solver.
      iDestruct (LocState_OwnOrig with "HLs") as %Horigs.
      assert (EV_Orig add_2_ev = 1%nat); last congruence.
      apply Horigs; set_solver.
    - iDestruct "Hstate" as (ev) "[(%&%Hev_val&%) Htk]"; simplify_eq.
      assert (add_2_ev = ev) as <- by set_solver.
      assert ({[add_2_ev]} ∪ s3 = {[add_2_ev]}) as Hunion_eq by set_solver.
      rewrite Hunion_eq in Hst.
      rewrite /crdt_denot /= /ctr_denot elements_singleton /= /ctr_payload Hev_val in Hst; subst.
      rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
      iMod ("Hclose" with "[HGs Htk]") as "_".
      { iNext. iExists _; iFrame "HGs"; eauto 10. }
      iModIntro.
      do 2 wp_pure _.
      wp_apply assert_proof.wp_assert.
      wp_pures. iSplit; first done.
      iNext; iApply "HΦ"; done.
    - iDestruct "Hstate" as (ev1 ev2) "[(%&%Hev1_val&%&%Hev2_val&%) [Htk1 Htk2]]"; simplify_eq.
      iDestruct (LocState_OwnOrig with "HLs") as %Horigs.
      assert (EV_Orig add_2_ev = 1%nat).
      { apply Horigs; set_solver. }
      assert (add_2_ev = ev1 ∨ add_2_ev = ev2) as [|] by set_solver; [congruence|subst].
      assert ({[ev2]} ∪ s3 = {[ev2]} ∨ {[ev2]} ∪ s3 = {[ev1; ev2]}) as Hunion_eq.
      { destruct (decide (ev1 ∈ s3)).
        - right; set_solver.
        - left; set_solver. }
      destruct Hunion_eq as [Hunion_eq|Hunion_eq].
      + rewrite Hunion_eq in Hst.
        rewrite /crdt_denot /= /ctr_denot elements_singleton /= /ctr_payload Hev2_val in Hst; subst.
        rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
        iMod ("Hclose" with "[HGs Htk1 Htk2]") as "_".
        { iNext. iExists _; iFrame "HGs"; iRight; iRight; iRight; iExists _, _; iFrame; eauto. }
        iModIntro.
        do 2 wp_pure _.
        wp_apply assert_proof.wp_assert.
        wp_pures. iSplit; first done.
        iNext; iApply "HΦ"; done.
      + assert (ev1 ≠ ev2) by congruence.
        rewrite Hunion_eq in Hst.
        rewrite /crdt_denot /= /ctr_denot in Hst.
        erewrite ctr_value_perm in Hst; last by apply elements_disj_union; set_solver.
        rewrite !elements_singleton /= /ctr_payload Hev1_val Hev2_val in Hst.
        rewrite /StLib_St_Coh /= /Ctr_St_Coh in Hop; subst.
        iMod ("Hclose" with "[HGs Htk1 Htk2]") as "_".
        { iNext. iExists _; iFrame "HGs"; iRight; iRight; iRight; iExists _, _; iFrame; eauto. }
        iModIntro.
        do 2 wp_pure _.
        wp_apply assert_proof.wp_assert.
        wp_pures. iSplit; first done.
        iNext; iApply "HΦ"; done.
  Qed.

End use_case_proof.




Section program_proof.
  Context `{!anerisG M Σ} `{!inG Σ (exclR unitO)}.
  Context `{!@StLibG (prodOp gctr_op gctr_op pnctr_op_pred) _ _ Σ}.
  Context `{uig: !utils.Internal_StLibG (prodOp gctr_op gctr_op pnctr_op_pred) Σ}.

  Notation pnOp := (prodOp gctr_op gctr_op pnctr_op_pred).
  Notation pnSt := (prodSt gctr_st gctr_st).
  Notation pnParams := (prod_params gctr_op gctr_st gctr_op gctr_st pnctr_op_pred).

  Definition Sn (n: nat) : (gset (fin n)).
  Proof.
    induction n.
    + exact (∅: gset (fin O)).
    + exact (( {[ nat_to_fin (Nat.lt_0_succ n)]}: gset (fin (S n)))
            ∪ (set_map FS IHn)).
  Defined.

  Lemma Sn_prop: forall n, ∀ (f: fin n), f ∈ (Sn n).
  Proof.
    induction n; intros x; first inversion x.
    destruct (resources_allocation.destruct_fin _ x) as [Hx | [x' Hx]];
      simplify_eq/=; set_solver.
  Qed.

  Lemma S_to_Sn: forall n S, (∀ (f: fin n), f ∈ S) -> S = Sn n.
  Proof.
    induction n as [|n IHn]; simplify_eq/=; intros S HS; apply set_eq; intros x;
      first by inversion x.
    split; destruct (resources_allocation.destruct_fin _ x) as [Hx | [x' Hx]];
      simplify_eq/=.
    - set_solver.
    - intros Hx'. apply elem_of_union_r, elem_of_map_2, Sn_prop.
    - intros _. apply HS.
    - intros [Himp|Hx']%elem_of_union; first set_solver. apply HS.
  Qed.

  Lemma S2_eq : forall S, (forall (f: fin 2), f ∈ S) -> S = ({[Ofin; Ifin]}: gset (fin 2)).
  Proof.
    intros S Hs.
    rewrite (S_to_Sn 2 S Hs).
    set_solver.
  Qed.

  Lemma wp_use_case_program E:
    ⊢ |={E}=> ∃ Res : StLib_Res pnOp,
         ([∗ list] i↦z ∈ CRDT_Addresses, z ⤇ StLib_SocketProto) -∗
         free_ip "1.1.1.1" -∗
         free_ip "1.1.1.2" -∗
         SocketAddressInet "1.1.1.1" 100 ⤳ (∅, ∅) -∗
         SocketAddressInet "1.1.1.2" 100 ⤳ (∅, ∅) -∗
         WP use_case_program @["system"]
      {{ v, ⌜v = #()⌝ }}.
  Proof.
    iIntros "".
    iMod (@StLibSetup_Init
            pnOp pnSt
            _ _ _ _ _ pnc_use_case_CRDT_Params (prod_lattice (vectn_le_lat ((length CRDT_Addresses))) (vectn_le_lat ((length CRDT_Addresses))))
            pnParams  _ _ E with "[//]")
      as (ResProd) "(#HGinvProd & HGsPRod & HtksProd & #HinitProd)".
    rewrite /init. simpl in *.
    iExists ResProd.
    iModIntro.
    iIntros "#Hprotos Hfip1 Hfip2 Hsa1 Hsa2".
    iDestruct "HtksProd" as (S) "(%Hfin & HitksProd)".
    simpl in *. simplify_eq /=.
    rewrite (S2_eq _ Hfin).
    Check FS.
    iAssert (StLib_InitToken Ofin ∗ StLib_InitToken Ifin)%I with "[HitksProd]"
      as "[Hitk1Prod Hitk2Prod]".
    { iDestruct (big_sepS_union with "HitksProd") as "[H1 H2]"; first set_solver.
      iDestruct ((bi.equiv_entails_1_1 _ _ ( big_sepS_singleton  _ _)) with "H1")
        as "H1".
      iDestruct ((bi.equiv_entails_1_1 _ _ ( big_sepS_singleton  _ _)) with "H2")
        as "H2".
      iFrame. }
    rewrite /use_case_program.
    iMod (own_alloc (Excl ())) as (γ1) "Htk1"; first done.
    iMod (own_alloc (Excl ())) as (γ2) "Htk2"; first done.
    iMod (inv_alloc use_case_inv_name _ (use_case_inv γ1 γ2) with "[HGsPRod]") as "#Hinv".
    { iNext. iExists ∅.  iFrame. iLeft; done. }
    wp_apply aneris_wp_start; first done.
    iSplitL "Hfip1"; first by iNext.
    iSplitR "Hitk1Prod Hsa1 Htk1"; last first.
    { iNext. iIntros "Hfps".
      iApply (wp_use_case_program1 with "[$Hsa1 $Hitk1Prod $Htk1 $Hfps][]"); last eauto.
      iFrame "#".
      iSplit.
      iApply pncounter_init_crdt_spec. rewrite /pn_prod_init_crdt_spec.
      iApply pn_init_spec. iFrame "#". eauto. }
    iNext.
    wp_pures.
    wp_apply aneris_wp_start; first done.
    iSplitL "Hfip2"; first by iNext.
    iSplit; first done.
    iNext. iIntros "Hfps".
    iApply (wp_use_case_program2 with "[$Hsa2 $Htk2 $Hitk2Prod $Hfps][]"); last eauto.
      iFrame "#".
      iSplit.
      iApply pncounter_init_crdt_spec. rewrite /pn_prod_init_crdt_spec.
      iApply pn_init_spec. iFrame "#". eauto.
  Qed.

End program_proof.


Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use := {["1.1.1.1" := ∅; "1.1.1.2" := ∅ ]};
    state_ms := ∅;
  |}.

Definition Trivial_Mdl : resources.Model :=
  {| model_state := ();
    model_rel := λ _ _, True;
    model_state_initial := (); |}.

Lemma Trivial_Mdl_finitary : aneris_model_rel_finitary Trivial_Mdl.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.


Definition use_case_Σ := #[anerisΣ Trivial_Mdl;  @OPLIBΣ CtrOp _ _; GFunctor (exclR unitO)].

Theorem use_case_program_adequate :
  aneris_adequate use_case_program "system" init_state (λ v, v = #()).
Proof.
  eapply (@adequacy
            use_case_Σ Trivial_Mdl _ _ {["1.1.1.1"; "1.1.1.2"]}
            (list_to_set addresses) ∅ ∅ ∅);
    [apply Trivial_Mdl_finitary| |set_solver..|done|done].
  iIntros (HanerisG) "".
  iModIntro.
  iIntros "Hfx Hsas _ Hfips _ _ _ _ _".
  rewrite big_sepS_union; last set_solver.
  rewrite !big_sepS_singleton.
  unfold addresses.
  iDestruct "Hfips" as "[Hfip1 Hfip2]".
  iAssert (SocketAddressInet "1.1.1.1" 100 ⤳ (∅, ∅) ∗
           SocketAddressInet "1.1.1.2" 100 ⤳ (∅, ∅))%I with "[Hsas]" as "[Hsa1 Hsa2]".
  { rewrite !list_to_set_cons list_to_set_nil right_id_L.
    rewrite big_sepS_union; last set_solver.
    rewrite !big_sepS_singleton.
    repeat (rewrite bool_decide_eq_false_2; last set_solver).
    done. }
  iMod wp_use_case_program as (Res) "Hwp".
  iDestruct (unallocated_split with "Hfx") as "[Hfx0 Hfx]"; [set_solver|].
  iDestruct (unallocated_split with "Hfx") as "[Hfx1 _]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton
            (@StLib_SocketProto _ _ _ _ _ _ _ Res) with "Hfx0").
  iIntros "#Hsi0".
  iApply (aneris_wp_socket_interp_alloc_singleton
            (@StLib_SocketProto _ _ _ _ _ _ _ Res) with "Hfx1").
  iIntros "#Hsi1".
  iAssert ([∗ list] i↦z ∈ addresses, z ⤇ (@StLib_SocketProto _ _ _ _ _ _ _ Res))%I as "Hprotos".
  { repeat iSplit; done. }
  wp_apply ("Hwp" with "Hprotos Hfip1 Hfip2 Hsa1 Hsa2").
  Unshelve.
  - apply subG_OPLIBΣ. admit.
  - admit.
Admitted.

From iris.algebra Require Import agree gmap auth.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     network tactics proofmode lifting lang.
From aneris.aneris_lang.lib Require Import lock_proof network_util_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec resources.
From aneris.examples.ccddb.examples.session_guarantees
     Require Import res sm_code sm_proof.
From aneris.examples.ccddb Require Import spec_util.

Context `{!anerisG Mdl Σ, !lockG Σ}.
Context `{!DB_params}.
Context `{!DB_time, !DB_events}.
Context `{!DB_resources Mdl Σ}.
Context `{!Maximals_Computing}.
Context `{!inG Σ (authUR (gmapUR nat (agreeR (leibnizO log_req))))}.

Section WritesFollowReads.

  (* We assume that the set of db keys is non-empty and we know two keys *)
  Variable key1 key2: Key.
  Hypothesis Hkey1_valid : key1 ∈ DB_keys.
  Hypothesis Hkey2_valid : key2 ∈ DB_keys.
  (* We assume a value that can be written to the db. *)
  Variable dbv2 : SerializableVal.

  Definition wfr_example : val :=
    λ: "client_addr" "server_addr1",
    let: "ops" := sm_setup "client_addr" in
    let: "init_fn" := Fst (Fst "ops") in
    let: "read_fn" := Snd (Fst "ops") in
    let: "write_fn" := Snd "ops" in
    "init_fn" "server_addr1";;
    let: "res" := "read_fn" "server_addr1" #key1 in
    "write_fn" "server_addr1" #key2 dbv2;;
    "res".

  Theorem wfr_example_spec (ca sa1 : socket_address)
          (db_id1 : rep_id) :
    {{{ sa1 ⤇ (db_si db_id1)
        ∗ unallocated {[ca]}
        ∗ free_ports (ip_of_address ca) {[ port_of_address ca ]}
        ∗ ca ⤳ (∅, ∅)
    }}}

      wfr_example #ca #sa1 @[ip_of_address ca]

    {{{ vo, RET vo;
        ∃ e2 s1,
          (Seen db_id1 s1)
            ∗ (⌜AE_key e2 = key2⌝)
            ∗ (⌜AE_val e2 = dbv2⌝)
            ∗ (⌜e2 ∈ s1⌝)
            ∗ (
              (* Read returns NONE *)
              (⌜vo = NONEV⌝)
              ∨
              (* Read returns SOME *)
              (∃ e1 v,
                  (⌜vo = SOMEV v⌝)
                    ∗ (⌜e1 ∈ s1⌝)
                    ∗ (⌜AE_key e1 = key1⌝)
                    ∗ (⌜AE_val e1 = v⌝)
                    ∗ (⌜e1 <ₜe2⌝)
              (* If sufficient time passes, then the two events
                 are propagated to db2 in the same order. *)
                    ∗ (∀ e s2 db_id2,
                          ((Seen db_id2 s2)
                            ∗ (⌜e ∈ s2⌝)
                            ∗ (⌜e2 ≤ₜe⌝))
                          ={⊤}=∗
                              ∃ e1' e2',
                                (⌜erasure e1' = erasure e1⌝)
                                  ∗ (⌜erasure e2' = erasure e2⌝)
                                  ∗ ⌜e1' ∈ s2⌝
                                  ∗ ⌜e2' ∈ s2⌝
                                  ∗ ⌜e1' <ₜe2'⌝)
                      )
            )
   }}}.
  Proof.
    iIntros (ϕ) "(#Hsi1 & Hca & Hfree & Hrs) Hcont".
    wp_lam. wp_pures.
    wp_apply (sm_setup_spec with "[$Hfree $Hca $Hrs]").
    iIntros (fns) "Hpre".
    iDestruct "Hpre" as (init_fn read_fn write_fn)
                          "(-> & #Hinit_spec & #Hread_spec & #Hwrite_spec)".
    wp_pures.
    (* Weaken postcondition to reason about fancy updates in e.g.
       strong extensionality *)
    wp_apply aneris_wp_fupd.
    (* Init *)
    wp_apply ("Hinit_spec" with "[$Hsi1]").
    rewrite /init_post.
    iIntros "Hinit". iDestruct "Hinit" as (s) "(#Hseen1 & #Hkeys1 & #Hinv)".
    (* Get snapshot for the key1 *)
    iAssert (∃ h : gmem, OwnMemSnapshot key1 h)%I as "#Hsnap1";
    first by iDestruct (big_sepS_delete _ _ _ Hkey1_valid with "Hkeys1") as "[Hkey1 _]".
    iDestruct "Hsnap1" as (h) "#Hsnap1".
    (* Get snapshot for the key2 *)
    iAssert (∃ h : gmem, OwnMemSnapshot key2 h)%I as "#Hsnap2";
    first by iDestruct (big_sepS_delete _ _ _ Hkey2_valid with "Hkeys1") as "[Hkey2 _]".
    iDestruct "Hsnap2" as (h2) "#Hsnap2".
    (* Read *)
    simpl. wp_pures.
    wp_apply ("Hread_spec" with "[$Hsi1 $Hseen1 $Hsnap1]"); [by iPureIntro|].
    iIntros (vo) "Hreadpost".
    iDestruct "Hreadpost" as (s' h') "(%Hss' & %Hhh' & #Hseen1' & #Hsnap1' & #Hreadpost)".
    simpl.
    (* Write *)
    wp_pures.
    wp_apply ("Hwrite_spec" $! _ _ _  dbv2 with "[$Hsi1 $Hseen1' $Hsnap2]"); [by iPureIntro|].
    iIntros "Hwritepost".
    iDestruct "Hwritepost" as (e2 s'' h2') "(%He2k & %He2v & %Hss'' & %Hh2'
    & #Hseen'' & #Hsnap2' & %He2s & %He2s' & %He2h2 & %He2h2' & %He2maxh & %He2maxs)".
    (* Prove postcondition *)
    wp_pures.
    (* State strong extensionality for s2'' *)
    iDestruct (Seen_strong_ext _ _ _ ⊤ with "Hinv Hseen'' Hseen''") as "> %Hseen_ext"; [done|].
    iModIntro.
    (* Prove properties of the write *)
    iApply "Hcont".
    iExists e2, s''.
    iSplitL; [iFrame "#"|].
    do 3 (iSplitL; [by iPureIntro|]).
    (* Consider two cases, depending on whether the read returned something
       or not. *)
    iDestruct "Hreadpost" as "[[-> %Hress'] | Hsome]"; [by iLeft|].
    iRight.
    iDestruct "Hsome" as (er vr) "(-> & %Herv & %Herk & %Hermax & %Hererasure)".
    (* The read returns something *)
    iExists er, vr.
    iSplitL; [done|].
    assert (er ∈ s'') as Hers''.
    { apply elem_of_Maximals in Hermax.
      apply elem_of_filter in Hermax.
      destruct Hermax as (_ & Hermax).
      set_solver.
    }
    iSplitL; [done|].
    do 2 (iSplitL; [by iPureIntro|]).
    assert (er <ₜ e2) as Herlt.
    { (* Show that the read and the write are ordered. *)
      apply Maximum_correct in He2maxs.
      - rewrite /IsMaximum in He2maxs.
        destruct He2maxs as (_ & He2maxs).
        apply He2maxs; [assumption|].
        intros Hereq.
        subst.
        apply He2s.
        apply elem_of_Maximals in Hermax.
        apply elem_of_filter in Hermax.
        destruct Hermax as (_ & Hermax).
        assumption.
      - intros.
        apply Hseen_ext; auto.
    }
    iSplitL; [by iPureIntro|].
    iIntros (ef sf db_id2) "(#Hseenf & %Hefs & %He2le)".
    (* State causality *)
    iDestruct (Causality _ _ _ _ ⊤ with "Hinv Hseenf Hsnap1'") as "> %Hcaus";
      [done|].
    iDestruct (Causality _ _ _ _ ⊤ with "Hinv Hseenf Hsnap2'") as "> %Hcaus2";
      [done|].
    (* Use causality to show that the er is in sf *)
    assert (erasure er <ₜ ef) as Herlt2.
    { apply (TM_lt_le_trans _ (time e2)  _); [| assumption].
        by (rewrite erasure_time).
    }
    destruct (Hcaus _ _ Hererasure Hefs Herlt2) as (er' & Her'_in_sf & Her_erase_eq).
    apply elem_of_filter in Her'_in_sf.
    destruct Her'_in_sf as (_ & Her'_in_sf).
    (* Split on whether e2 and ef occur at the same time *)
    destruct (TM_le_eq_or_lt _ _ He2le) as [Heq | Hlt].
    - (* e2 and ef happen at the same time *)
      iDestruct (Seen_provenance _ _ _ ⊤ with "Hinv Hseenf") as "Prov";
        [auto | apply Hefs |].
      iMod "Prov" as (hf) "[Hsnapf %Hefinh]".
      iDestruct (Snapshot_ext _ _ _ _ ⊤ with "Hinv Hsnap2' Hsnapf") as "Hext"; [done|].
      iMod "Hext" as "%Hext".
      assert ((erasure e2) = (erasure ef)) as Herasure_eq.
      { apply Hext; auto.
        rewrite (erasure_time e2).
        rewrite (erasure_time ef).
        assumption.
      }
      iModIntro.
      iExists er', ef.
      iPureIntro.
      repeat split; auto.
      rewrite -(erasure_time er').
      by rewrite Her_erase_eq.
    - (* e2 happens before ef *)
      assert (erasure e2 <ₜef) as He2_erasure_lt;
        [by (rewrite erasure_time)|].
      destruct (Hcaus2 _ _ He2h2' Hefs He2_erasure_lt) as (e2' & He2'_in_sf & He2'_erasure_eq).
      apply elem_of_filter in He2'_in_sf.
      destruct He2'_in_sf as (_ & He2'_in_sf).
      iModIntro.
      iExists er', e2'.
      iPureIntro.
      repeat split; try assumption.
      rewrite -(erasure_time er').
      rewrite -(erasure_time e2').
      rewrite Her_erase_eq. rewrite He2'_erasure_eq.
      rewrite (erasure_time er).
        by rewrite (erasure_time e2).
  Qed.

End WritesFollowReads.

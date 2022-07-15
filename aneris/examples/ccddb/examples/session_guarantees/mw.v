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

Section MonotonicWrites.

  (* We assume that the set of db keys is non-empty and we know two of the keys *)
  Variable key1 : Key.
  Hypothesis Hkey_valid1 : key1 ∈ DB_keys.
  Variable key2 : Key.
  Hypothesis Hkey_valid2 : key2 ∈ DB_keys.
  (* We assume a couple of values that can be written to the db. *)
  Variable dbv1 : SerializableVal.
  Variable dbv2 : SerializableVal.

  (* Monotonic writes example *)
  Definition mw_example : val :=
    λ: "client_addr" "server_addr1",
    let: "ops" := sm_setup "client_addr" in
    let: "init_fn" := Fst (Fst "ops") in
    let: "read_fn" := Snd (Fst "ops") in
    let: "write_fn" := Snd "ops" in
    "init_fn" "server_addr1";;
    "write_fn" "server_addr1" #key1 dbv1;;
    "write_fn" "server_addr1" #key2 dbv2.

  Theorem mw_example_spec (A : gset socket_address) (ca sa1 : socket_address)
          (db_id1 : rep_id) :
    {{{ sa1 ⤇ (db_si db_id1)
        ∗ unfixed {[ca]}
        ∗ free_ports (ip_of_address ca) {[ port_of_address ca ]}
        ∗  ca ⤳ (∅, ∅)
    }}}

      mw_example #ca #sa1 @[ip_of_address ca]

   {{{ RET #();
        ∃ s1 e1 e2,
         (* The writes are observed in db1 *)
         (⌜AE_val e1 = dbv1⌝)
           ∗ (⌜AE_key e1 = key1⌝)
           ∗ (⌜AE_val e2 = dbv2⌝)
           ∗ (⌜AE_key e2 = key2⌝)
           ∗ Seen db_id1 s1
           ∗ ⌜e1 ∈ s1⌝
           ∗ ⌜e2 ∈ s1⌝
           ∗ (⌜e1 <ₜe2⌝)
           (* If sufficient time passes, then the writes
              are propagated to db2 in the same order. *)
           ∗ (∀ e s2 db_id2,
                 (Seen db_id2 s2
                       ∗ ⌜e ∈ s2⌝
                       ∗ ⌜e2 ≤ₜe⌝) ={⊤}=∗
                                   ∃ e1' e2',
                                     (⌜erasure e1' = erasure e1⌝)
                                       ∗ (⌜erasure e2' = erasure e2⌝)
                                       ∗ ⌜e1' ∈ s2⌝
                                       ∗ ⌜e2' ∈ s2⌝
                                       ∗ ⌜e1' <ₜe2'⌝)
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
    (* Get snapshot for the keys we want to write to *)
    (* First key *)
    iAssert (∃ h : gmem, OwnMemSnapshot key1 h)%I as "#Hsnap1";
    first by iDestruct (big_sepS_delete _ _ _ Hkey_valid1 with "Hkeys1") as "[Hkey1 _]".
    iDestruct "Hsnap1" as (h1) "#Hsnap1".
    (* Second key *)
    iAssert (∃ h : gmem, OwnMemSnapshot key2 h)%I as "#Hsnap2";
    first by iDestruct (big_sepS_delete _ _ _ Hkey_valid2 with "Hkeys1") as "[Hkey2 _]".
    iDestruct "Hsnap2" as (h2) "#Hsnap2".
    simpl. wp_pures.
    (* First write *)
    wp_apply ("Hwrite_spec" $! _ _ key1 dbv1 with "[$Hsi1 $Hseen1 $Hsnap1]"); [by iPureIntro |].
    iIntros "Hwpost1". rewrite /write_post.
    iDestruct "Hwpost1" as  (e1 s1 h1') "(%Hek1 & %Hev1 & %Hss1 & %Hhh1 &
    #Hseen1' & #Hsnap1' & %Hes1 & %Hes1' & %Heh1 & %Heh1' & %Hemaxh1 & %Hemaxs1)".
    (* Second write *)
    wp_pures.
    wp_apply ("Hwrite_spec" $! _ _ key2 dbv2 with "[$Hsi1 $Hseen1' $Hsnap2]"); [by iPureIntro| ].
    iIntros "Hwpost2". rewrite /write_post.
    iDestruct "Hwpost2" as  (e2 s2 h2') "(%Hek1' & %Hev1' & %Hss1' & %Hhh1' &
    #Hseen1'' & #Hsnap1'' & %Hes1'' & %Hes1''' & %Heh1'' & %Heh1''' & %Hemaxh1' & %Hemaxs1')".
    (* Proving the postcondition *)
    iApply "Hcont".
    (* We need strong extensionality in s1' later on to prove the two writes are ordered *)
    iDestruct (Seen_strong_ext _ _ _ ⊤ with "Hinv Hseen1'' Hseen1''") as "> %Htimeseq"; [done|].
    iExists s2, e1, e2.
    iAssert (⌜e1 ∈ s2⌝%I) as "%Hin"; [by iPureIntro; set_solver|].
    iAssert (⌜e2 ∈ s2⌝%I) as "%Hin'"; [by iPureIntro|].
    iAssert (⌜e1 <ₜ e2⌝%I) as "%He1lte2".
    { apply Maximum_correct in Hemaxs1'.
      * rewrite /IsMaximum in Hemaxs1'.
        destruct Hemaxs1' as (Hin'' & Hlt).
        iPureIntro.
        apply Hlt; auto.
        intros Heq.
          by subst.
      * intros x y Hx Hy Heqt.
        apply Htimeseq; auto.
    }
    iFrame "#".
    do 7 (iApply fupd_sep; iSplitL; [by iPureIntro|]).
    iModIntro.
    iIntros (er sr db_id2) "(#Hseenr & %Herin & %Hlter)".
    (* State causality *)
    iDestruct (Causality _ _ _ _ ⊤ with "Hinv Hseenr Hsnap1'") as "#Hcaus1"; [set_solver|].
    iDestruct (Causality _ _ _ _ ⊤ with "Hinv Hseenr Hsnap1''") as "#Hcaus2"; [set_solver|].
    (* State strong ext *)
    iDestruct (Seen_provenance _ _ _ ⊤ with "Hinv Hseenr") as "#Hsnapr"; [auto | eauto |].
    iMod "Hsnapr" as (hr) "(#Hsnapr & %Herasurer)".
    iDestruct (Snapshot_ext _ _ _ _ ⊤ with "Hinv Hsnap1'' Hsnapr") as "#Hext"; [set_solver|].
    iMod "Hcaus1"; iMod "Hcaus2"; iMod "Hext"; iModIntro.
    iDestruct "Hcaus1" as %Hcaus1.
    iDestruct "Hcaus2" as %Hcaus2.
    iDestruct "Hext" as %Hext.
    (* Apply causality twice *)
    (* First apply causality result of the first write *)
    assert (erasure e1 ∈ h1') as He1inh1' by set_solver.
    assert (erasure e1 <ₜ er) as He1lter.
    { rewrite (erasure_time e1).
        by apply (TM_lt_le_trans _ (time e2) _).
    }
    pose proof (Hcaus1 _ er He1inh1' Herin He1lter) as
        [e1copy (He1in & Herasuree1)].
    (* Now we have two cases, either e2 is = to er, or it's less than *)
    destruct (TM_le_eq_or_lt _ _ Hlter) as [He2eq | He2lt].
      * (* Eq case *)
        iExists e1copy, er.
        repeat iSplit; auto; iPureIntro.
        ** symmetry.
           apply Hext; auto.
           rewrite (erasure_time e2).
           rewrite (erasure_time er).
           done.
        ** apply elem_of_filter in He1in.
           by destruct He1in as (_ & H1in).
        ** rewrite <- (erasure_time e1copy).
           rewrite Herasuree1.
           rewrite (erasure_time e1).
           apply (TM_lt_le_trans _ (time e2) _); auto.
      * (* Lt case *)
        (* We apply causality again *)
        assert (erasure e2 <ₜ er) as Herasurelt;
            [by (rewrite (erasure_time e2))|].
        pose proof (Hcaus2 _ er Heh1''' Herin Herasurelt) as
            [e2copy (He2in & Herasuree2)].
        iExists e1copy, e2copy.
        iPureIntro.
        repeat split; auto.
        ** apply elem_of_filter in He1in.
           by destruct He1in as (_ & He1in).
        ** apply elem_of_filter in He2in.
           by destruct He2in as (_ & He1'in).
        ** rewrite <- (erasure_time e1copy).
           rewrite <- (erasure_time e2copy).
           rewrite Herasuree1. rewrite Herasuree2.
           rewrite (erasure_time e1). rewrite (erasure_time e2).
           assumption.
  Qed.

End MonotonicWrites.

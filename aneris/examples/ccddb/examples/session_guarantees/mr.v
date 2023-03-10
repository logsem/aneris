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

Section MonotonicReads.

  (* We assume that the set of db keys is non-empty and we know one of the keys *)
  Variable key : Key.
  Hypothesis Hkey_valid : key ∈ DB_keys.

  (* Monotonic reads example *)
  Definition mr_example : val :=
    λ: "client_addr" "server_addr",
    let: "ops" := sm_setup "client_addr" in
    let: "init_fn" := Fst (Fst "ops") in
    let: "read_fn" := Snd (Fst "ops") in
    let: "write_fn" := Snd "ops" in
    "init_fn" "server_addr";;
    let: "v1" := "read_fn" "server_addr" #key in
    let: "v2" := "read_fn" "server_addr" #key in
    ("v1", "v2").

  Theorem mr_example_spec (A : gset socket_address) (ca sa : socket_address) (db_id : rep_id) :
    {{{ sa ⤇ (db_si db_id)
        ∗ unallocated {[ca]}
        ∗ unbound (ip_of_address ca) {[ port_of_address ca ]}
        ∗ ca ⤳ (∅, ∅)
    }}}

      mr_example #ca #sa @[ip_of_address ca]

   {{{ p, RET p;
       ∃ vo1 vo2,
         (⌜p = (vo1, vo2)%V⌝)
           ∗ ((* Both reads return NONE, and the db's entry for the key is empty *)
              (∃ s,
                  (⌜vo1 = NONEV⌝)
                    ∗ (⌜vo2 = NONEV⌝)
                    ∗ Seen db_id s
                    ∗ (⌜restrict_key key s = ∅⌝))
              ∨
              ((* The first read returns NONE, and the second returns a value with maximal
                timestamp *)
                ∃ s v2 e,
                (⌜vo1 = NONEV⌝)
                  ∗ (⌜vo2 = SOMEV v2⌝)
                  ∗ Seen db_id s
                  ∗ (⌜AE_key e = key⌝)
                  ∗ (⌜AE_val e = v2⌝)
                  ∗ (⌜e ∈ Maximals (restrict_key key s)⌝)
              )
              ∨
              ((* Both reads return some value, and the second read returns a value that's not
                older than the first one (could be the same, more recent, or incomparable) *)
                ∃ s v1 v2 e1 e2,
                  (⌜vo1 = SOMEV v1⌝)
                    ∗ (⌜vo2 = SOMEV v2⌝)
                    ∗ Seen db_id s
                    ∗ (⌜AE_key e1 = key⌝)
                    ∗ (⌜AE_val e1 = v1⌝)
                    ∗ (⌜AE_key e2 = key⌝)
                    ∗ (⌜AE_val e2 = v2⌝)
                    ∗ (⌜e2 ∈ Maximals (restrict_key key s)⌝)
                    ∗ (⌜¬ (e2 <ₜe1)⌝)
              )
   ) }}}.
  Proof.
    iIntros (ϕ) "(#Hsi & Hca & Hfree & Hrs) Hcont".
    wp_lam. wp_pures.
    wp_apply (sm_setup_spec with "[$Hfree $Hca $Hrs]").
    iIntros (fns) "Hpre".
    iDestruct "Hpre" as (init_fn read_fn write_fn)
                          "(-> & #Hinit_spec & #Hread_spec & #Hwrite_spec)".
    wp_pures.
    (* Init *)
    wp_apply ("Hinit_spec" with "[$Hsi]").
    rewrite /init_post.
    iIntros "Hinit". iDestruct "Hinit" as (s) "(#Hseen & #Hkeys & _)".
    (* Get snapshot for the key we want to read *)
    iAssert (∃ h : gmem, OwnMemSnapshot key h)%I as "#Hsnap";
    first by iDestruct (big_sepS_delete _ _ _ Hkey_valid with "Hkeys") as "[Hkey _]".
    iDestruct "Hsnap" as (h) "#Hsnap".
    (* First read *)
    wp_pures.
    wp_apply ("Hread_spec" with "[$Hsi $Hseen $Hsnap]"); [by iPureIntro |].
    iIntros (vo) "Hreadpost".
    rewrite /read_post.
    iDestruct "Hreadpost" as (s' h') "(#Hss' & #Hhh' & #Hseen' &
    #Hsnap' & [[-> #Hrestrict'] | Hsome'])"; simpl; wp_pures.
    - (* First read returns NONE *)
      (* Second read *)
      wp_apply ("Hread_spec" with "[$Hsi $Hseen' $Hsnap']"); [by iPureIntro |].
      iIntros (vo) "Hreadpost".
      rewrite /read_post.
      iDestruct "Hreadpost" as (s'' h'') "(#Hss'' & #Hhh'' & #Hseen'' &
      #Hsnap'' & [[-> #Hrestrict''] | Hsome''])"; wp_pures; iApply "Hcont".
      * (* Second read returns NONE *)
        iExists _, _. iSplit; first by iPureIntro.
        iLeft; eauto.
      * (* Second read returns SOME *)
        iExists _, _. iSplit; first by eauto.
        iDestruct "Hsome''" as (e2 v2) "(-> & #Hval2 & #Hkey2 & #Hmax2 & _)".
        iRight. iLeft. iExists _, _, _.
        iFrame "#". eauto.
    - (* First read returns SOME *)
      (* Second read *)
      wp_apply ("Hread_spec" with "[$Hsi $Hseen' $Hsnap']"); [by iPureIntro |].
      iIntros (vo2) "Hreadpost".
      rewrite /read_post.
      iDestruct "Hreadpost" as (s'' h'') "(#Hss'' & #Hhh'' & #Hseen'' &
      #Hsnap'' & [[-> #Hrestrict''] | Hsome''])"; wp_pures; iApply "Hcont".
      * (* Second read returns NONE: contradiction *)
        iDestruct "Hrestrict''" as %Hrestrict''.
        iDestruct "Hss''" as %Hss''.
        iDestruct "Hsome'" as (e' v') "(_ & #Hv' & #Hk' & #Hmax' & _)".
        iDestruct "Hmax'" as %Hmax'.
        exfalso.
        apply elem_of_Maximals in Hmax'.
        apply (restrict_key_mono _ _ _ _ Hss'') in Hmax'.
        set_solver.
      * (* Second read returns SOME *)
        iExists _, _.
        iSplit; first auto.
        iRight; iRight.
        iDestruct "Hsome'" as (e' v') "(-> & #Hv1 & #Hk1 & #Hmax1 & _)".
        iDestruct "Hsome''" as (e'' v'') "(-> & #Hv2 & #Hk2 & #Hmax2 & _)".
        iExists _, v', v'', e', e''.
        do 2 (iSplit; first auto).
        iFrame "#".
        iDestruct "Hmax2" as %Hmax2.
        iDestruct "Hmax1" as %Hmax1.
        iDestruct "Hss''" as %Hss''.
        iPureIntro.
        apply elem_of_Maximals in Hmax1.
        apply (restrict_key_mono _ _ _ _ Hss'') in Hmax1.
        apply Maximals_correct in Hmax2.
        destruct Hmax2 as (_ & Hforall).
          by apply Hforall.
    Qed.

End MonotonicReads.

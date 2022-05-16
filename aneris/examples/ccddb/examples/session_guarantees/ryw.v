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

Section ReadYourWrites.

  (* We assume that the set of db keys is non-empty and we know one of the keys *)
  Variable key : Key.
  Hypothesis Hkey_valid : key ∈ DB_keys.
  (* We assume a value that can be written to the db. *)
  Variable dbv : SerializableVal.

  (* Read Your Writes example *)
  Definition ryw_example : val :=
    λ: "client_addr" "server_addr",
    let: "ops" := sm_setup "client_addr" in
    let: "init_fn" := Fst (Fst "ops") in
    let: "read_fn" := Snd (Fst "ops") in
    let: "write_fn" := Snd "ops" in
    "init_fn" "server_addr";;
    "write_fn" "server_addr" #key dbv;;
    "read_fn" "server_addr" #key.

  Theorem ryw_example_spec (A : gset socket_address) (ca sa : socket_address) (db_id : rep_id) :
    {{{ fixed A
        ∗ ⌜sa ∈ A⌝
        ∗ sa ⤇ (db_si db_id)
        ∗ ⌜ca ∉ A⌝
        ∗ free_ports (ip_of_address ca) {[ port_of_address ca ]}
        ∗ ca ⤳ (∅, ∅)
    }}}

      ryw_example #ca #sa @[ip_of_address ca]

   {{{ vo, RET vo;
       ∃ s e e' v, ⌜vo = SOMEV v⌝
                 ∗ ⌜AE_val e = v⌝
                 ∗ ⌜AE_key e = key⌝
                 ∗ ⌜AE_val e' = dbv⌝
                 ∗ ⌜AE_key e' = key⌝
                 ∗ Seen db_id s
                 ∗ ⌜e ∈ s⌝
                 ∗ ⌜e' ∈ s⌝
                 ∗ ⌜¬ (e <ₜe')⌝
   }}}.
  Proof.
    iIntros (ϕ) "(#Hfixed & #Hsa & #Hsi & #Hca & Hfree & Hrs) Hcont".
    wp_lam. wp_pures.
    wp_apply (sm_setup_spec with "[$Hfree $Hfixed $Hca $Hrs]").
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
    wp_pures.
    (* Write *)
    wp_apply ("Hwrite_spec" $! _ _ key dbv with "[$Hsi $Hseen $Hsnap]"); [by iPureIntro|].
    iIntros "Hwpost". rewrite /write_post.
    iDestruct "Hwpost" as  (e' s' h') "(#Hek' & #Hev' & #Hss' & _ &
    #Hseen' & #Hsnap' & #Hes & #Hes' & #Hemaxh & #Hemaxs')".
    (* Read *)
    wp_pures.
    wp_apply ("Hread_spec" with "[$Hsi $Hseen' $Hsnap']"); [by iPureIntro|].
    iIntros (vo) "Hreadpost". iApply "Hcont".
    rewrite /read_post.
    iDestruct "Hreadpost" as (s'' h'') "(#Hss'' & _ & #Hseen'' &
    _ & [[-> #Hrestrict] | Hsome])".
    - (* Read returns none: a contradiction *)
      iDestruct "Hrestrict" as %Hrestrict.
      iDestruct "Hss''" as %Hss''.
      iDestruct "Hes'" as %Hes'.
      iDestruct "Hek'" as %Hek'.
      exfalso.
      assert (e' ∈ s'') as Hes'' by set_solver.
      assert (e' ∈ restrict_key key s'') as Hinrest; last by set_solver.
      apply (iffRL (elem_of_filter _ _ _)); auto.
    - (* Read returns some value *)
      iDestruct "Hsome" as (e'' v'') "(-> & #Hev'' & #Hek'' & #Hemax & #Herasure)".
      iExists s'', e'', e', _.
      iSplit; first by iPureIntro.
      iFrame "#".
      iDestruct "Hemax" as %Hemax.
      iDestruct "Hes'" as %Hes'.
      iDestruct "Hss''" as %Hss''.
      iDestruct "Hek'" as %Hek'.
      iDestruct "Hek''" as %Hek''.
      repeat iPureIntro.
      repeat split; auto.
      * assert (e'' ∈ restrict_key key s'') as Hin.
        { eapply Maximals_correct in Hemax.
          destruct Hemax as (? & _); auto.
        }
        set_solver.
      * eapply Maximals_correct in Hemax.
        destruct Hemax as (Hinres & Hforall).
        apply Hforall.
        assert (e' ∈ s'') as He'in by set_solver.
        eapply elem_of_filter; auto.
  Qed.

End ReadYourWrites.

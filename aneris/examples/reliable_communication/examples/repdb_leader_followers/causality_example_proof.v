From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.prelude Require Import list.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting aneris_adequacy.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import prelude ras.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model repdb_code.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import ras events resources api_spec.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import proof_of_db_init.
From aneris.examples.reliable_communication.examples.repdb_leader_followers
     Require Import causality_example_code.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.

Section proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si follower_si : message → iProp Σ).
  Context (db_l2csa db_f2csa db_l2fsa : socket_address).

  (* ------------------------------------------------------------------------ *)
  (** The definition of the parameters for DB and DL and shared resources. *)
  (* ------------------------------------------------------------------------ *)

  Local Instance DBSrv : DB_params :=
    {|
      DB_addr := db_l2csa;
      DB_addrF := db_l2fsa;
      DB_followers := {[db_f2csa]};
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!@DB_resources _ _ _ _ DBSrv}.

  Definition N := nroot.@"y".

  Lemma wp_wait_on_read clt_00 fsa rd h0:
    GlobalInv -∗
    (∀ k h, read_at_follower_spec rd clt_00 fsa k h) -∗
    {{{ Obs fsa h0 }}}
      wait_on_read rd #"y" #1 @[ip_of_address clt_00]
    {{{ h' a, RET #();
        ⌜h0 `prefix_of` h'⌝ ∗ Obs fsa h' ∗
        ⌜(we_val a) = #1⌝ ∗ ⌜at_key "y" h' = Some a⌝ }}}.
  Proof.
    iIntros "#HGinv #Hard".
    iIntros "!>" (Φ) "#HobsF HΦ".
    wp_lam. wp_pures.
    iLöb as "IH".
    wp_apply ("Hard" $! "y" ); [done|done|]; iIntros (w).
    iDestruct 1 as (h') "(%Hprefix & #HobsF' &
                           [(-> & %Hatkey)|(%a & -> & %Hatkey)]) /=".
    { wp_pures. iApply ("IH" with "HΦ"). }
    wp_pures.
    case_bool_decide as Ha.
    { wp_pures. iApply "HΦ". by naive_solver. }
    wp_pures. iApply ("IH" with "HΦ").
  Qed.

  Definition inv_def : iProp Σ :=
    ("y" ↦ₖ None) ∨
    (∃ h hfx hfy we_y we_x,
        "y" ↦ₖ Some we_y ∗ "x" ↦ₖ Some we_x ∗
        Obs db_l2csa (h ++ [we_x] ++ hfx ++ [we_y] ++ hfy) ∗
        ⌜we_val we_x = #37⌝ ∗
        ⌜at_key "x" h = None⌝ ∗ ⌜at_key "y" h = None⌝ ∗
        ⌜at_key "x" hfx = None⌝ ∗ ⌜at_key "y" hfx = None⌝ ∗
        ⌜at_key "x" hfy = None⌝ ∗ ⌜at_key "y" hfy = None⌝).

  Lemma wp_do_writes wr clt_00 :
    GlobalInv -∗
    inv N inv_def -∗
    write_spec wr clt_00 -∗
    Obs db_l2csa [] -∗
    {{{ "x" ↦ₖ None }}}
      do_writes wr @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HGinv #Hinv #Hwr #Hobs".
    iIntros "!>" (Φ) "Hx HΦ".
    iDestruct (get_simplified_write_spec with "Hwr") as "#Hswr".
    iDestruct (write_spec_write_spec_atomic with "Hwr") as "#Hawr".
    iClear "Hwr".
    wp_lam.
    wp_apply ("Hswr" $! _ (SerVal #37) with "[] [Hx]"); [done| |].
    { iExists _. by iFrame "#∗". }
    iDestruct 1 as (h a Hkey Hval Hatkey) "[#Hobs' Hx]".
    wp_pures.
    wp_apply ("Hawr" $! (⊤ ∖ ↑N) _ (SerVal #1)); [solve_ndisj|done|].
    iInv N as "IH" "Hclose".
    iDestruct "IH" as "[>Hy | >IH]"; last first.
    { iDestruct "IH" as (h' hfx hfy we_y we_x) "(Hy & Hx' & _)".
      by iDestruct (OwnMemKey_exclusive with "Hx Hx'") as "[]". }
    iMod (OwnMemKey_none_obs with "HGinv [$Hy $Hobs']") as "[Hy %Hhist]";
      [solve_ndisj|].
    assert (at_key "y" ([] ++ h ++ [a]) = None) as Hatkey'.
    { rewrite /at_key. by rewrite Hhist. }
    iModIntro.
    iExists ([] ++ h ++ [a]), None.
    iFrame "#∗". iSplit; [done|].
    iNext.
    iIntros (h'' a').
    iDestruct 1 as (Hatkey''' Hkey' Hval' Hle) "[Hy #Hobs'']".
    iMod (OwnMemKey_some_obs_frame with "HGinv [$Hx Hobs'']")
      as "[Hx %Hatkey'''']"; [solve_ndisj| |].
    { assert (([] ++ h ++ [a]) ++ h'' ++ [a'] =
              (([] ++ h) ++ [a] ++ (h'' ++ [a']))) as ->;
        [by rewrite !assoc|done]. }
    assert (at_key "x" h'' = None).
    { rewrite at_key_snoc_none in Hatkey''''; [done|by rewrite Hkey']. }
    iMod ("Hclose" with "[-HΦ]"); [|by iApply "HΦ"].
    iNext. iRight. iExists h, h'', [], a', a.
    rewrite !app_assoc.
    iFrame "#∗".
    rewrite hist_at_key_empty_at_key in Hhist.
    rewrite at_key_snoc_none in Hhist; [done|by rewrite Hkey].
  Qed.

  Lemma wp_do_reads clt_01 rd fsa :
    GlobalInv -∗
    (∀ k h, read_at_follower_spec rd clt_01 fsa k h) -∗
    inv N inv_def -∗
    Obs fsa [] -∗
    {{{ True }}}
      do_reads rd @[ip_of_address clt_01]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HGinv #Hard #Hinv_y #Hobs0".
    iIntros "!>" (Φ) "_ HΦ".
    wp_lam.
    wp_apply (wp_wait_on_read); [done..|].
    iIntros (h a) "(_ & #Hobs & _ & %Hatkey)".
    wp_pures.
    wp_apply ("Hard" $! "x"); [done..|].
    iIntros (vo) "H".
    iDestruct "H" as (h' Hprefix) "(#Hobs' & %Hdisj)".
    iApply fupd_aneris_wp.
    iInv N as "HI" "Hclose".
    iDestruct "HI" as "[>Hy|>HI]".
    { iMod (OwnMemKey_none_obs with "HGinv [$Hy $Hobs]")as "[Hy %Hhist]";
        [solve_ndisj|].
      by rewrite /at_key Hhist in Hatkey. }
    iDestruct "HI" as (hb hfx hfy we_y we_x)
                        "(Hy & Hx & #Hobs'' & %Hval &
                        %Hatkey_hbx & %Hatkey_hby &
                        %Hatkey_hfxx & %Hatkey_hfxy &
                        %Hatkey_hfyx & %Hatkey_hfyy)".
    iMod (OwnMemKey_key with "HGinv Hx") as "[Hx %Hkey_x]"; [solve_ndisj|].
    iMod (OwnMemKey_key with "HGinv Hy") as "[Hy %Hkey_y]"; [solve_ndisj|].
    assert (at_key "y" (hb ++ [we_x] ++ hfx ++ [we_y] ++ hfy) = Some we_y)
           as Hatkey_y.
    { rewrite /at_key.
      rewrite hist_at_key_frame_l_prefix; [|done].
      rewrite hist_at_key_frame_l_prefix; last first.
      { rewrite /at_key /hist_at_key.
        rewrite filter_cons_False; [done|by rewrite Hkey_x]. }
      rewrite hist_at_key_frame_l_prefix; [|done].
      rewrite hist_at_key_frame_r_suffix; [|done].
      rewrite /at_key /hist_at_key.
      rewrite filter_cons_True; [done|by rewrite Hkey_y]. }
    assert (at_key "x" (hb ++ [we_x] ++ hfx ++ [we_y] ++ hfy) = Some we_x)
           as Hatkey_x.
    { rewrite /at_key.
      rewrite hist_at_key_frame_l_prefix; [|done].
      rewrite hist_at_key_frame_r_suffix.
      { rewrite /at_key /hist_at_key.
        rewrite filter_cons_True; [done|by rewrite Hkey_x]. }
      rewrite /at_key.
      rewrite hist_at_key_frame_l_prefix; [|done].
      rewrite hist_at_key_frame_r_suffix; [|done].
      rewrite /at_key /hist_at_key.
      rewrite filter_cons_False; [done|by rewrite Hkey_y]. }
    iAssert ("y" ↦ₖ Some we_y ={⊤ ∖ ↑N}=∗ ⌜a = we_y⌝ ∗ "y" ↦ₖ Some we_y)%I
      as "H".
    { iDestruct (Obs_compare with "Hobs Hobs''") as %Hprefix'.
      iIntros "Hy".
      destruct Hprefix' as [Hprefix'|Hprefix'].
      - iModIntro. iFrame "Hy". iPureIntro.
        rewrite !assoc in Hprefix'.
        rewrite -assoc in Hprefix'.
        eapply prefix_split_eq; [apply Hatkey| |done|apply Hprefix'].
        rewrite !filter_app.
        rewrite /at_key /hist_at_key !last_None in
          Hatkey_hbx Hatkey_hby Hatkey_hfxx Hatkey_hfyx
                     Hatkey_hfyy Hatkey_hfxy.
        rewrite Hatkey_hby Hatkey_hfxy.
        rewrite filter_cons_False; [done| by rewrite Hkey_x].
      - rewrite -Hatkey_y.
        iMod (OwnMemKey_obs_frame_prefix with "HGinv [$Hy $Hobs]")
          as "[Hy %Heq]"; [solve_ndisj|done|].
        rewrite -Heq in Hatkey.
        rewrite Hatkey in Hatkey_y.
        iModIntro.
        iFrame "Hy".
        iPureIntro.
        by simplify_eq. }
    iMod ("H" with "Hy") as (->) "Hy". iClear "H".
    assert (∃ ao : option we,
                at_key "x" h' = ao ∧
                ((vo = InjLV #() ∧ ao = None) ∨
                 (∃ a : we, vo = InjRV (we_val a) ∧ ao = Some a)))
      as [a [Hatkey_a Hdisj']].
    { destruct Hdisj as [Hdisj | Hdisj].
      - destruct Hdisj as [-> Hdisj]. exists None. split; [done|by left].
      - destruct Hdisj as [a [-> Hdisj]]. exists (Some a).
        split; [done|by right;eexists _]. }
    iAssert ("x" ↦ₖ Some we_x ={⊤ ∖ ↑N}=∗ ⌜a = Some we_x⌝ ∗ "x" ↦ₖ Some we_x)%I
      as "H".
    { iDestruct (Obs_compare with "Hobs' Hobs''") as %Hprefix'.
      iIntros "Hx".
      destruct Hprefix' as [Hprefix'|Hprefix'].
      - iModIntro. iFrame "Hx". iPureIntro.
        assert (h `prefix_of` hb ++ [we_x] ++ hfx ++ [we_y] ++ hfy) as Hprefix''.
        { by eapply transitivity. }
        rewrite !assoc in Hprefix''.
        rewrite -assoc -assoc in Hprefix''.
        assert (((hb ++ [we_x])) `prefix_of` h) as Hprefix'''.
        { eapply prefix_Some_None.
          - apply Hatkey.
          - rewrite !filter_app.
            rewrite /at_key /hist_at_key !last_None in
              Hatkey_hbx Hatkey_hby Hatkey_hfxx Hatkey_hfyx
                         Hatkey_hfyy Hatkey_hfxy.
            rewrite Hatkey_hby.
            rewrite filter_cons_False; [done|by rewrite Hkey_x].
          - apply Hprefix''. }
        destruct Hprefix''' as [k ->].
        assert (∃ a', at_key "x" h' = Some a') as [a' Hatkey_a'].
        { destruct Hprefix as [k' ->].
          eapply (elem_of_last_filter_exists_Some _ _ a we_x).
          - apply Hatkey_a.
          - set_solver.
          - done. }
        assert (a = Some a') as -> by naive_solver.
        f_equiv.
        eapply prefix_split_eq; [apply Hatkey_a'|apply Hatkey_hbx| |apply Hprefix'].
        + rewrite !filter_app.
          rewrite /at_key /hist_at_key !last_None in
            Hatkey_hbx Hatkey_hby Hatkey_hfxx Hatkey_hfyx
                       Hatkey_hfyy Hatkey_hfxy.
          rewrite Hatkey_hfxx Hatkey_hfyx.
          rewrite filter_cons_False; [done|by rewrite Hkey_y].
      - rewrite -Hatkey_x.
        iMod (OwnMemKey_obs_frame_prefix with "HGinv [$Hx $Hobs']")
          as "[Hy %Heq]"; [solve_ndisj|done|].
        rewrite -Heq in Hatkey_a.
        rewrite Hatkey_a in Hatkey_x.
        iModIntro.
        iFrame "Hy".
        iPureIntro.
        by simplify_eq. }
    iMod ("H" with "Hx") as (->) "Hx". iClear "H".
    destruct Hdisj' as [[_ Hineq]|Hdisj']; [done|].
    destruct Hdisj' as [a [-> Heq]].
    assert (we_x = a) as <-.
    { by simplify_eq. }
    iMod ("Hclose" with "[Hx Hy]") as "_".
    { iRight. iExists _, _, _, _, _. by iFrame "Hx Hy #". }
    iModIntro.
    do 2 wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    rewrite Hval.
    iSplit; [done|].
    by iApply "HΦ".
  Qed.

  Lemma proof_of_node0 (clt_00 : socket_address) :
    GlobalInv -∗
    init_client_proxy_leader_spec leader_si -∗
    Obs db_l2csa [] -∗
    inv N inv_def -∗
    {{{ unallocated {[clt_00]} ∗
        free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        db_l2csa ⤇ leader_si ∗
        "x" ↦ₖ None }}}
      node0 #clt_00 #db_l2csa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HGinv #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hf & Hfps & Hclt00 & #Hsi & Hx) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[$Hf $Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (wr rd) "[_ Hwr]".
    wp_pures.
    iApply (wp_do_writes with "[$] [$] [$] [$] Hx HΦ").
  Qed.

  Lemma proof_of_node1 (clt_01 : socket_address) :
    GlobalInv -∗
    init_client_proxy_follower_spec db_f2csa follower_si -∗
    Obs db_f2csa [] -∗
    inv N inv_def -∗
    {{{ unallocated {[clt_01]} ∗
        free_ports (ip_of_address clt_01) {[port_of_address clt_01]} ∗
        clt_01 ⤳ (∅, ∅) ∗
        db_f2csa ⤇ follower_si }}}
      node1 #clt_01 #db_f2csa @[ip_of_address clt_01]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HGinv #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hf & Hfps & Hclt00 & #Hsi) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[$Hf $Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (rd) "#Hrd".
    wp_pures.
    by iApply wp_do_reads.
  Qed.

End proof_of_code.

(** Concrete parameters (addresses, ips) *)
Definition db_l2csa := SocketAddressInet "0.0.0.0" 80.
Definition db_l2fsa := SocketAddressInet "0.0.0.0" 81.
Definition db_f2lsa := SocketAddressInet "0.0.0.1" 80.
Definition db_f2csa := SocketAddressInet "0.0.0.1" 81.
Definition clt_sa0 := SocketAddressInet "0.0.0.2" 80.
Definition clt_sa1 := SocketAddressInet "0.0.0.3" 80.
Definition A : gset socket_address := {[ db_l2csa; db_l2fsa; db_f2csa ]}.
Definition addrs : gset socket_address :=
  {[ db_f2lsa; clt_sa0; clt_sa1; db_l2csa; db_l2fsa; db_f2csa ]}.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"; "0.0.0.2"; "0.0.0.3" ]}.
Global Instance DBP : DB_params := DBSrv db_l2csa db_f2csa db_l2fsa.

Definition main : expr :=
    Start "0.0.0.0" (init_leader (DB_serialization.(s_serializer))
                                 #db_l2csa #db_l2fsa);;
    Start "0.0.0.1" (init_follower (DB_serialization.(s_serializer)) #db_l2fsa
                                   #db_f2lsa #db_f2csa);;
    Start "0.0.0.2" (node0 #clt_sa0 #db_l2csa);;
    Start "0.0.0.3" (node1 #clt_sa1 #db_f2csa).


Section proof_of_main.
  Context `{!anerisG Mdl Σ, lockG Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si leaderF_si follower_si : message → iProp Σ).
  Context (InitL InitF : iProp Σ).
  Context `{DBRes : !@DB_resources _ _ _ _ DBP}.

  Lemma main_spec :
    ⊢ |={⊤}=>
         GlobalInv -∗
         init_leader_spec InitL leader_si leaderF_si -∗
         init_client_proxy_leader_spec leader_si -∗
         init_follower_spec db_f2csa InitF follower_si leaderF_si -∗
         init_client_proxy_follower_spec db_f2csa follower_si -∗
         db_l2csa ⤇ leader_si -∗
         db_l2fsa ⤇ leaderF_si -∗
         db_f2csa ⤇ follower_si -∗
         unallocated {[db_f2lsa;clt_sa0;clt_sa1]} -∗
         Obs db_l2csa [] -∗
         Obs db_f2csa [] -∗
         inv N (inv_def db_l2csa db_f2csa db_l2fsa) -∗
         free_ip "0.0.0.0" -∗
         free_ip "0.0.0.1" -∗
         free_ip "0.0.0.2" -∗
         free_ip "0.0.0.3" -∗
         SocketAddressInet "0.0.0.0" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.0" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.3" 80 ⤳ (∅, ∅) -∗
         InitL -∗
         InitF -∗
         "x" ↦ₖ None -∗
         WP main @["system"]
      {{ v, True }}.
  Proof.
    iIntros "".
    iModIntro.
    iIntros "#HGinv #HdbSrvS #HdbCltS #HdbFS #HdbCltF".
    iIntros "#Hdb_l2csa #Hdb_l2fsa #Hdb_f2csa Hf #HobsL #HobsF #HI".
    iIntros "Hfree0 Hfree1 Hfree2 Hfree3".
    iIntros "Hsa0 Hsa1 Hsa2 Hsa3 Hsa4 Hsa5 HInitL HInitF".
    iIntros "Hx".
    rewrite /main.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree0".
    iSplitR "Hsa0 Hsa1 HInitL"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbSrvS"
               with "[][][HInitL Hsa0 Hfps Hsa1]"); [eauto .. | | done ].
      iDestruct (free_ports_split
                    "0.0.0.0"
                    {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iFrame "#∗". iApply "Hfp1". iFrame. }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive;81%positive]}); first done.
    iFrame "Hfree1".
    iDestruct (unallocated_split with "Hf") as "[Hf Hf1]"; [set_solver|].
    iDestruct (unallocated_split with "Hf") as "[Hff2lsa Hf0]"; [set_solver|].
    iSplitR "Hsa2 Hsa3 HInitF Hff2lsa"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbFS" $! db_f2lsa with "[//][][Hfps HInitF Hsa2 Hsa3 Hff2lsa]");
        [iPureIntro; set_solver| |done].
      iDestruct (free_ports_split
                   "0.0.0.1"
                   {[80%positive]} {[81%positive]} with "Hfps")
        as "(Hfp1 & Hfp2)"; [set_solver|].
      iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}); first done.
    iFrame "Hfree2".
    iSplitR "Hsa4 Hx Hf0"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node0 leader_si db_l2csa db_f2csa db_l2fsa clt_sa0
               with "HGinv HdbCltS HobsL HI [Hf0 Hsa4 Hfps Hx]");
        [ |done].
      iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}); first done.
    iFrame "Hfree3".
    iSplitR "Hsa5 Hf1"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node1 follower_si db_l2csa db_f2csa db_l2fsa clt_sa1
               with "HGinv HdbCltF HobsF HI [Hf1 Hsa5 Hfps]");
        [ |done].
      iFrame "#∗". }
    done.
  Qed.

End proof_of_main.

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $
      <["0.0.0.1" := ∅ ]> $
      <["0.0.0.2" := ∅ ]> $
      <["0.0.0.3" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition dummy_model := model unit (fun x y => True) ().

Lemma dummy_model_finitary : adequacy.aneris_model_rel_finitary dummy_model.
Proof.
  intros st.
  intros f Hnot.
  pose proof (Hnot 0%nat 1%nat) as H.
  assert (0%nat = 1%nat -> False) as Himpl. {
    intros Heq.
    discriminate Heq.
  }
  apply Himpl; apply H.
  destruct (f 0%nat) as [s0 r0].
  destruct (f 1%nat) as [s1 r1].
  destruct s0, s1, st, r0, r1.
  reflexivity.
Qed.

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; DBΣ; SpecChanΣ ]).
  eapply (@adequacy
            Σ dummy_model _ _ ips addrs _
            ∅ ∅);
    [ | | set_solver.. ].
  { apply dummy_model_finitary. }
  iIntros (Hdg) "".
  assert (DBPreG Σ) as HPreG by apply _.
  iMod (DB_init_setup ⊤) as (DBRes) "Hdb";
    [solve_ndisj|set_solver|set_solver| ].
  iDestruct "Hdb"
    as (InitL leader_si leaderF_si) "(#HGinv & #Hobs & Hkeys & HInitL &
                                      #[HinitL_spec HinitL_proxy_spec] &
                                      HF)".
  rewrite big_sepS_singleton.
  iDestruct "HF" as (follower_si InitF) "(HInitF & #HobsF &
                                          #HinitF_spec & #HinitF_proxy_spec)".
  (* iExists (socket_interp leader_si leaderF_si follower_si). *)
  iMod (@main_spec
          _ _ _
          int_time leader_si leaderF_si follower_si InitL InitF DBRes) as "Hmain".
  iModIntro.
  iIntros "Hf Hb Hfg Hips _ _ _ _ _".
  rewrite /addrs.
  iDestruct (unallocated_split with "Hf") as "[Hf Hff2csa]"; [set_solver|].
  iDestruct (unallocated_split with "Hf") as "[Hf Hfl2fsa]"; [set_solver|].
  iDestruct (unallocated_split with "Hf") as "[Hf Hfl2csa]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton follower_si with "Hff2csa").
  iIntros "Hsi2".
  iApply (aneris_wp_socket_interp_alloc_singleton leaderF_si with "Hfl2fsa").
  iIntros "Hsi1".
  iApply (aneris_wp_socket_interp_alloc_singleton leader_si with "Hfl2csa").
  iIntros "Hsi0".
  iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "[Hip0 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "[Hip1 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.2" with "Hips") as "[Hip2 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.3" with "Hips") as "[Hip3 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_l2csa with "Hb") as "[Hm0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_l2fsa with "Hms") as "[Hm1 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_f2lsa with "Hms") as "[Hm2 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_f2csa with "Hms") as "[Hm3 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa0 with "Hms") as "[Hc0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa1 with "Hms") as "[Hc1 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "x" with "Hkeys") as "[Hx Hkeys]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "y" with "Hkeys") as "[Hy _]";
   first set_solver.
  iMod (inv_alloc N _ (inv_def db_l2csa db_f2csa db_l2fsa) with "[Hy]") as "HI".
  { by iLeft. }
  iApply ("Hmain" with
           "HGinv HinitL_spec HinitL_proxy_spec HinitF_spec HinitF_proxy_spec
            Hsi0 Hsi1 Hsi2 Hf Hobs HobsF HI Hip0 Hip1 Hip2 Hip3
            Hm0 Hm1 Hm2 Hm3 Hc0 Hc1 HInitL HInitF Hx").
Qed.

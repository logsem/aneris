From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import ras events resources api_spec.
From aneris.examples.reliable_communication.examples.repdb_leader_followers
     Require Import causality_example_code.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.

Section helper_lemmas.

  Lemma prefix_Some_None {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys zs x :
    last (filter P xs) = Some x →
    last (filter P ys) = None →
    xs `prefix_of` ys ++ zs →
    ys `prefix_of` xs.
  Proof.
    intros Hsome Hnone Hprefix.
    rewrite last_None in Hnone.
    generalize dependent xs.
    induction ys as [|y ys]; intros xs Hsome Hprefix.
    { by apply prefix_nil. }
    destruct xs as [|x' xs]; [done|].
    assert (y = x') as <-.
    { by apply prefix_cons_inv_1 in Hprefix. }
    apply prefix_cons.
    rewrite filter_cons in Hnone.
    apply prefix_cons_inv_2 in Hprefix.
    rewrite filter_cons in Hsome.
    apply IHys; [by destruct (decide (P y))|by destruct (decide (P y))|done].
  Qed.

  Lemma prefix_cons_nil {A:Type} (xs : list A) y ys :
    xs ≠ [] →
    xs `prefix_of` y :: ys →
    [y] `prefix_of` xs.
  Proof.
    intros Hneq Hprefix.
    destruct xs; [done|].
    apply prefix_cons_inv_1 in Hprefix.
    rewrite Hprefix.
    by apply prefix_cons, prefix_nil.
  Qed.

  Lemma last_filter_app_r {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys x :
    last (filter P (xs ++ ys)) = Some x →
    last (filter P xs) = None →
    last (filter P ys) = Some x.
  Proof.
    intros Hsome Hnone%last_None.
    by rewrite filter_app Hnone in Hsome.
  Qed.

  Lemma prefix_split_eq {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys zs x y :
    last (filter P xs) = Some x →
    last (filter P ys) = None →
    last (filter P zs) = None →
    xs `prefix_of` ys ++ [y] ++ zs →
    x = y.
  Proof.
    intros Hsome Hnone1 Hnone2 Hprefix.
    assert (ys `prefix_of` xs) as [k ->].
    { by eapply prefix_Some_None. }
    apply prefix_app_inv in Hprefix.
    apply last_filter_app_r in Hsome; [|done].
    assert ([y] `prefix_of` k) as [k' ->].
    { eapply prefix_cons_nil; [|done]. by intros ->. }
    rewrite filter_app in Hsome.
    rewrite last_None in Hnone2.
    apply prefix_app_inv in Hprefix.
    destruct Hprefix as [k'' ->].
    rewrite filter_app in Hnone2.
    apply app_eq_nil in Hnone2.
    destruct Hnone2 as [Hnone2 _].
    rewrite Hnone2 in Hsome.
    rewrite filter_cons in Hsome.
    destruct (decide (P y)); [|done].
    simpl in *. by simplify_eq.
  Qed.

  Lemma elem_of_last_filter_exists_Some
        {A} `{EqDecision A} (P : A → Prop) `{!∀ x, Decision (P x)} xs x y :
    last (filter P xs) = x →
    y ∈ xs → P y →
    ∃ x', last (filter P xs) = Some x'.
  Proof.
    intros Hlast Hin HPy.
    induction xs as [|z xs IHxs]; [by set_solver|].
    destruct (decide (P z)) as [HPz|HPz].
    - rewrite filter_cons_True; [|done].
      assert (last (filter P xs) = None ∨
              ∃ x', last (filter P xs) = Some x') as Hfilter.
      { by destruct (last (filter P xs)); [right; eexists _|left]. }
      destruct Hfilter as [Hnone|[x' Hsome]].
      + exists z. rewrite last_None in Hnone. by rewrite Hnone.
      + exists x'. rewrite last_cons. by rewrite Hsome.
    - rewrite filter_cons_False; [|done].
      rewrite filter_cons_False in Hlast; [|done].
      assert (y ≠ z) as Hneq.
      { intros Heq. by simplify_eq. }
      apply elem_of_cons in Hin.
      destruct Hin as [Hin|Hin]; [done|by apply IHxs].
  Qed.

End helper_lemmas.

Section proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si follower_si : message → iProp Σ).
  Context (db_sa db_Fsa db_saF : socket_address).

  (* ------------------------------------------------------------------------ *)
  (** The definition of the parameters for DB and DL and shared resources. *)
  (* ------------------------------------------------------------------------ *)

  Local Instance DBSrv : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_saF;
      DB_followers := {[db_Fsa]};
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
        Obs db_sa (h ++ [we_x] ++ hfx ++ [we_y] ++ hfy) ∗
        ⌜we_val we_x = #37⌝ ∗
        ⌜at_key "x" h = None⌝ ∗ ⌜at_key "y" h = None⌝ ∗
        ⌜at_key "x" hfx = None⌝ ∗ ⌜at_key "y" hfx = None⌝ ∗
        ⌜at_key "x" hfy = None⌝ ∗ ⌜at_key "y" hfy = None⌝).

  Lemma wp_do_writes wr clt_00 :
    GlobalInv -∗
    inv N inv_def -∗
    write_spec wr clt_00 -∗
    Obs db_sa [] -∗
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
    { iMod (Obs_compare with "HGinv Hobs Hobs''") as %Hprefix'; [solve_ndisj|].
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
    { iMod (Obs_compare with "HGinv Hobs' Hobs''") as %Hprefix'; [solve_ndisj|].
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

  Lemma proof_of_node0 (clt_00 : socket_address) A :
    db_sa ∈ A →
    clt_00 ∉ A →
    GlobalInv -∗
    fixed A -∗
    (∀ A ca, init_client_proxy_leader_spec A ca leader_si) -∗
    Obs db_sa [] -∗
    inv N inv_def -∗
    {{{ free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        db_sa ⤇ leader_si ∗
        "x" ↦ₖ None }}}
      node0 #clt_00 #db_sa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HIndb HnInA) "#HGinv #Hfixed #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hfps & Hclt00 & #Hsi & Hx) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[//] [//] [$Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (wr rd) "[_ Hwr]".
    wp_pures.
    iApply (wp_do_writes with "[$] [$] [$] [$] Hx HΦ").
  Qed.

  Lemma proof_of_node1 (clt_01 : socket_address) A :
    db_Fsa ∈ A →
    clt_01 ∉ A →
    GlobalInv -∗
    fixed A -∗
    (∀ A ca, init_client_proxy_follower_spec A ca db_Fsa follower_si) -∗
    Obs db_Fsa [] -∗
    inv N inv_def -∗
    {{{ free_ports (ip_of_address clt_01) {[port_of_address clt_01]} ∗
        clt_01 ⤳ (∅, ∅) ∗
        db_Fsa ⤇ follower_si }}}
      node1 #clt_01 #db_Fsa @[ip_of_address clt_01]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HIndb HnInA) "#HGinv #Hfixed #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hfps & Hclt00 & #Hsi) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[//] [//] [$Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (rd) "#Hrd".
    wp_pures.
    by iApply wp_do_reads.
  Qed.

End proof_of_code.

(* WIP going forward *)
(** Concrete parameters (addresses, ips) *)
Definition db_l2csa := SocketAddressInet "0.0.0.0" 80.
Definition db_l2fsa := SocketAddressInet "0.0.0.0" 81.
Definition db_f2lsa := SocketAddressInet "0.0.0.1" 80.
Definition db_f2csa := SocketAddressInet "0.0.0.1" 81.
Definition clt_sa0 := SocketAddressInet "0.0.0.2" 80.
Definition clt_sa1 := SocketAddressInet "0.0.0.3" 80.
Definition A : gset socket_address := {[ db_l2csa; db_l2fsa; db_f2csa ]}.
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

  Definition init_follower_spec f2lsa f2csa A initF f_si lF_si : iProp Σ :=
        ⌜DB_addrF ∈ A⌝ →
        ⌜f2csa ∈ A⌝ →
        ⌜f2lsa ∉ A⌝ →
        ⌜ip_of_address f2csa = ip_of_address f2lsa⌝ →
        ⌜port_of_address f2csa ≠ port_of_address f2lsa⌝ →
        {{{ fixed A ∗
            f2csa ⤇ f_si ∗
            DB_addrF ⤇ lF_si ∗
            initF ∗
            f2lsa ⤳ (∅, ∅) ∗
            f2csa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address f2csa) {[port_of_address f2csa]} ∗
            free_ports (ip_of_address f2lsa) {[port_of_address f2lsa]} }}}
          init_follower (s_serializer DB_serialization)
            #DB_addrF #f2lsa #f2csa @[ip_of_address f2csa]
        {{{ RET #(); True }}}.


  Lemma main_spec :
    ⊢ |={⊤}=>
         GlobalInv -∗
         (∀ A, init_leader_spec A InitL leader_si leaderF_si) -∗
         (∀ A, init_follower_spec db_f2lsa db_f2csa A InitF follower_si leaderF_si) -∗
         (∀ A ca, init_client_proxy_leader_spec A ca leader_si) -∗
         (∀ A ca, init_client_proxy_follower_spec A ca db_f2csa follower_si) -∗
         db_l2csa ⤇ leader_si -∗
         db_l2fsa ⤇ leaderF_si -∗
         db_f2csa ⤇ follower_si -∗
         fixed A -∗
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
    iIntros "#HGinv #HdbSrvS #HdbFS #HdbCltS #HdbCltF".
    iIntros "#Hdb_l2csa #Hdb_l2fsa #Hdb_f2csa #Hfixed #HobsL #HobsF #HI".
    iIntros "Hfree0 Hfree1 Hfree2 Hfree3".
    iIntros "Hsa0 Hsa1 Hsa2 Hsa3 Hsa4 Hsa5 HInitL HInitF".
    iIntros "Hx".
    rewrite /main.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree0".
    iSplitR "Hsa0 Hsa1 HInitL"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbSrvS" $! A
               with "[][][][][HInitL Hfps Hsa0 Hsa1]"); [eauto .. | | done ].
      iDestruct (free_ports_split
                    "0.0.0.0"
                    {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iFrame "#∗". iApply "Hfp1". iFrame. }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive;81%positive]}); first done.
    iFrame "Hfree1".
    iSplitR "Hsa2 Hsa3 HInitF"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbFS" $! A with "[//][//][][//][//][Hfps HInitF Hsa2 Hsa3]");
        [iPureIntro; set_solver| |done].
      iDestruct (free_ports_split
                   "0.0.0.1"
                   {[80%positive]} {[81%positive]} with "Hfps")
        as "(Hfp1 & Hfp2)"; [set_solver|].
      iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}); first done.
    iFrame "Hfree2".
    iSplitR "Hsa4 Hx"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node0 leader_si db_l2csa db_f2csa db_l2fsa clt_sa0 A
               with "HGinv Hfixed HdbCltS HobsL HI [Hsa4 Hfps Hx]");
        [done|set_solver| |done].
      iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}); first done.
    iFrame "Hfree3".
    iSplitR "Hsa5"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node1 follower_si db_l2csa db_f2csa db_l2fsa clt_sa1 A
               with "HGinv Hfixed HdbCltF HobsF HI [Hsa5 Hfps]");
        [done|set_solver| |done].
      iFrame "#∗". }
    done.
  Qed.

End proof_of_main.

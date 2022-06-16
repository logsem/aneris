From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
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
(*
Section API_spec_ext.
  Context `{!anerisG Mdl Σ, !DB_time, !DB_params, !DB_resources}.

  Definition write_spec
      (wr : val) (sa : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal)
         (P : iProp Σ) (Q : we → ghst → ghst → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P
            ={⊤, E}=∗
              ∃ (h : ghst) (a_old: option we),
                ⌜at_key k h = a_old⌝ ∗
                k ↦ₖ a_old ∗
                Obs DB_addr h ∗
                  ▷ (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ ∗
                  ⌜we_key a_new = k⌝ ∗
                  ⌜we_val a_new = v⌝ ∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                  k ↦ₖ Some a_new ∗
                  Obs DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf)) -∗
        {{{ P }}}
          wr #k v @[ip_of_address sa]
        {{{ RET #();
           ∃ (h hf : ghst) (a: we), Q a h hf }}})%I.

  Definition write_spec_atomic
      (wr : val) (sa : socket_address) : iProp Σ :=
    ∀ (E : coPset) (k : Key) (v : SerializableVal),
    ⌜↑DB_InvName ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h : ghst) (a_old : option we),
      ⌜at_key k h = a_old⌝ ∗
      k ↦ₖ a_old ∗
      Obs DB_addr h >>>
      wr #k v @[ip_of_address sa] E
    <<<▷ ∃∃ hf a_new, RET #();
           ⌜at_key k hf = None⌝ ∗
           ⌜we_key a_new = k⌝ ∗
           ⌜we_val a_new = v⌝ ∗
           ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
           k ↦ₖ Some a_new ∗
           Obs DB_addr (h ++ hf ++ [a_new]) >>>.

  Lemma write_spec_write_spec_atomic wr sa :
    write_spec wr sa -∗ write_spec_atomic wr sa.
  Proof.
    iIntros "#Hwr" (E k v HE Hkeys Φ) "!> Hvs".
    iApply ("Hwr" $! E k v _ (λ _ _ _, Φ #()) with "[] [] [] Hvs");
      [ done .. | | ].
    { iIntros "!> Hvs".
      iMod "Hvs" as (h a_old) "[(%Hatkey & Hk & Hobs) Hclose]".
      iModIntro.
      eauto 10 with iFrame. }
    iIntros "!> H".
    iDestruct "H" as (_ _ _) "H".
    iApply "H".
  Qed.

  Axiom write_spec_implies_simplified_write_spec : ∀ wr sa,
    write_spec wr sa -∗ ∀ k v h, simplified_write_spec wr sa k v h.

End API_spec_ext.

Section proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si follower_si : message → iProp Σ).
  Context (db_sa db_Fsa : socket_address).

  (* ------------------------------------------------------------------------ *)
  (** The definition of the parameters for DB and DL and shared resources. *)
  (* ------------------------------------------------------------------------ *)

  Local Instance DBSrv : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_Fsa;
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!@DB_resources _ _ _ _ DBSrv}.

  Definition token (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma token_exclusive (γ : gname) : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Definition Ny := nroot.@"y".
  Definition Nx := nroot.@"x".

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
    wp_lam.
    do 7 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply ("Hard" $! "y" ); [done|done|].
    iIntros (w).
    iDestruct 1 as (h') "(%Hprefix & #HobsF' & [(-> & %Hatkey)|(%a & -> & %Hatkey)]) /=".
    { do 7 wp_pure _. iApply ("IH" with "HΦ"). }
    wp_pures.
    case_bool_decide as Ha.
    { wp_pure _.
      iApply ("HΦ" $! h' a).
      naive_solver. }
    do 3 wp_pure _.
    iApply ("IH" with "HΦ").
  Qed.

  Definition inv_def : iProp Σ :=
    ("y" ↦ₖ None) ∨
    (∃ h hfx hfy we_y we_x,
        "y" ↦ₖ Some we_y ∗ "x" ↦ₖ Some we_x ∗
        Obs DB_addr (h ++ [we_x] ++ hfx ++ [we_y] ++ hfy) ∗
        ⌜we_val we_x = #37⌝ ∗
        ⌜at_key "x" h = None⌝ ∗ ⌜at_key "y" h = None⌝ ∗
        ⌜at_key "x" hfx = None⌝ ∗ ⌜at_key "y" hfx = None⌝ ∗
        ⌜at_key "x" hfy = None⌝ ∗ ⌜at_key "y" hfy = None⌝).

  Lemma wp_do_writes wr clt_00 :
    GlobalInv -∗
    inv Ny inv_def -∗
    write_spec wr clt_00 -∗
    Obs DB_addr [] -∗
    {{{ "x" ↦ₖ None }}}
      do_writes wr @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HGinv #Hinv #Hwr #Hobs".
    iIntros "!>" (Φ) "Hx HΦ".
    iDestruct (write_spec_implies_simplified_write_spec with "Hwr") as "#Hswr".
    iDestruct (write_spec_write_spec_atomic with "Hwr") as "#Hawr".
    iClear "Hwr".
    wp_lam.
    wp_apply ("Hswr" $! _ (SerVal #37) with "[] [Hx]"); [done| |].
    { iExists _. iFrame "#∗". done. }
    iDestruct 1 as (h a Hkey Hval Hatkey) "[#Hobs' Hx]".
    wp_pures.
    wp_apply ("Hawr" $! (⊤ ∖ ↑Ny) _ (SerVal #1)); [solve_ndisj|done|].
    iInv Ny as "IH" "Hclose".
    iDestruct "IH" as "[>Hy | >IH]"; last first.
    { iDestruct "IH" as (h' hfx hfy we_y we_x) "(Hy & Hx' & _)".
      iDestruct (OwnMemKey_exclusive with "Hx Hx'") as "[]". }
    iMod (OwnMemKey_none_obs with "HGinv [$Hy $Hobs']") as "[Hy %Hhist]";
      [solve_ndisj|].
    assert (at_key "y" ([] ++ h ++ [a]) = None).
    { rewrite /at_key. rewrite Hhist. done. }
    iModIntro.
    iExists ([] ++ h ++ [a]), None.
    iFrame "#∗".
    iSplit; [done|].
    iNext.
    iIntros (h'' a').
    iDestruct 1 as (Hatkey''' Hkey' Hval' Hle) "[Hy #Hobs'']".
    iMod (OwnMemKey_some_obs_frame with "HGinv [$Hx Hobs'']")
      as "[Hx %Hatkey'''']"; [solve_ndisj| |].
    { assert (([] ++ h ++ [a]) ++ h'' ++ [a'] =
              (([] ++ h) ++ [a] ++ (h'' ++ [a']))) as ->.
      { by rewrite !assoc. }
      done. }
    assert (at_key "x" h'' = None).
    { rewrite at_key_snoc_none in Hatkey''''; [done|].
      by rewrite Hkey'. }
    iMod ("Hclose" with "[-HΦ]"); [|by iApply "HΦ"].
    iNext.
    iRight.
    iExists h, h'', [], a', a.
    rewrite !app_assoc.
    iFrame "#∗".
    simpl in *.
    iSplit; [done|].
    iSplit; [done|].
    iSplit.
    { iPureIntro.
      rewrite hist_at_key_empty_at_key in Hhist.
      rewrite at_key_snoc_none in Hhist; [done| by rewrite Hkey]. }
    done.
  Qed.

  Lemma wp_do_reads clt_01 rd fsa :
    GlobalInv -∗
    (∀ k h, read_at_follower_spec rd clt_01 fsa k h) -∗
    inv Ny inv_def -∗
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
    wp_apply ("Hard" $! "x"); [done|done|].
    iIntros (vo) "H".
    iDestruct "H" as (h' Hprefix) "(#Hobs' & %Hdisj)".
    iApply fupd_aneris_wp.
    iInv Ny as "HI" "Hclose".
    iDestruct "HI" as "[>Hy|>HI]".
    { iMod (OwnMemKey_none_obs with "HGinv [$Hy $Hobs]")as "[Hy %Hhist]";
        [solve_ndisj|].
      rewrite /at_key in Hatkey.
      rewrite Hhist in Hatkey.
      done. }
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
      rewrite hist_at_key_frame_l_prefix; [|]; last first.
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

    iAssert ("y" ↦ₖ Some we_y ={⊤ ∖ ↑Ny}=∗ ⌜a = we_y⌝ ∗ "y" ↦ₖ Some we_y)%I
      as "H".
    { iMod (Obs_compare with "HGinv Hobs Hobs''") as %Hprefix'; [solve_ndisj|].
      iIntros "Hy".
      destruct Hprefix' as [Hprefix'|Hprefix'].
      - (* `h` is at least `hb ++ [we_x] ++ hfx ++ [we_y]`,
           and at_key "y" (hb ++ [we_x] ++ hfx) = None
           thus `at_key "y" h` can only be we_y *)
        iModIntro. iFrame "Hy". iPureIntro.

        rewrite /at_key /hist_at_key !last_None in
          Hatkey_hbx Hatkey_hby Hatkey_hfxx Hatkey_hfyx Hatkey_hfyy Hatkey_hfxy.
        clear Hatkey_x.
        clear Hatkey_y.
        clear Hatkey_hbx.
        clear Hatkey_hfxx.
        clear Hatkey_hfyx.
        clear Hprefix.

        assert (hb `prefix_of` h) as Hprefix''.
        {
          generalize dependent h.
          induction hb as [|v hb]; intros h Hatkey Hprefix'.
          { apply prefix_nil. }
          destruct h as [|w h]; [done|].
          assert (w = v) as <-.
          { rewrite !assoc in Hprefix'.
            by apply prefix_cons_inv_1 in Hprefix'. }
          apply prefix_cons.
          apply IHhb.
          - rewrite /hist_at_key in Hatkey_hby.
            rewrite filter_cons in Hatkey_hby.
            by destruct (decide (we_key w = "y")).
          - rewrite filter_cons in Hatkey_hby.
            destruct (decide (we_key w = "y")); [done|].
            rewrite /at_key in Hatkey.
            rewrite /hist_at_key in Hatkey.
            by rewrite filter_cons_False in Hatkey.
          - by apply prefix_cons_inv_2 in Hprefix'.
        }
        destruct Hprefix'' as [k ->].
        apply prefix_app_inv in Hprefix'.
        assert ([we_x] `prefix_of` k) as Hprefix''.
        { simpl in *.
          destruct k.
          { rewrite /at_key /hist_at_key in Hatkey.
            rewrite right_id in Hatkey.
            by rewrite Hatkey_hby in Hatkey. }
          apply prefix_cons_inv_1 in Hprefix'. simplify_eq.
          apply prefix_cons. apply prefix_nil. }
        destruct Hprefix'' as [k' ->].
        apply prefix_app_inv in Hprefix'.
        assert (hfx `prefix_of` k') as Hprefix''.
        {
          assert (at_key "y" k' = Some a) as Hatkey'.
          { rewrite /at_key /hist_at_key in Hatkey.
            rewrite filter_app in Hatkey.
            rewrite Hatkey_hby in Hatkey.
            rewrite filter_cons_False in Hatkey; [done|].
            rewrite Hkey_x. done. }
          generalize dependent k'.
          induction hfx; intros k' Hatkey Hprefix' Hatkey'.
          { apply prefix_nil. }
          destruct k'; [done|].
          assert (w = a0) as <-.
          { rewrite !assoc in Hprefix'.
            by apply prefix_cons_inv_1 in Hprefix'. }
          apply prefix_cons.
          apply IHhfx.
          - rewrite filter_cons in Hatkey_hfxy.
            by destruct (decide (we_key w = "y")).          
          - rewrite filter_cons in Hatkey_hfxy.
            rewrite /at_key in Hatkey'.
            destruct (decide (we_key w = "y")); [done|].
            rewrite /hist_at_key in Hatkey'.
            rewrite /at_key /hist_at_key.
            rewrite filter_app.
            rewrite Hatkey_hby.
            rewrite filter_cons_False; [|by rewrite Hkey_x].
            rewrite filter_cons_False in Hatkey'; [done|done].
          - by apply prefix_cons_inv_2 in Hprefix'.
          - rewrite filter_cons in Hatkey_hfxy.
            rewrite /at_key in Hatkey'.
            destruct (decide (we_key w = "y")); [done|].
            rewrite /hist_at_key in Hatkey'.
            rewrite filter_cons_False in Hatkey'; [done|done].
        }
        destruct Hprefix'' as [k'' ->].
        apply prefix_app_inv in Hprefix'.
        assert ([we_y] `prefix_of` k'') as Hprefix''.
        {
          destruct k''.
          {
            rewrite /at_key /hist_at_key filter_app in Hatkey.
            rewrite Hatkey_hby in Hatkey.
            rewrite filter_cons_False in Hatkey; [|by rewrite Hkey_x].
            rewrite right_id in Hatkey.
            rewrite Hatkey_hfxy in Hatkey.
            done. }
          apply prefix_cons_inv_1 in Hprefix'.
          subst. apply prefix_cons. apply prefix_nil.
        }
        destruct Hprefix'' as [k''' ->].
        apply prefix_app_inv in Hprefix'.
        destruct Hprefix' as [k'''' ->].
        rewrite filter_app in Hatkey_hfyy.
        apply app_eq_nil in Hatkey_hfyy.
        destruct Hatkey_hfyy as [Hatkey_hfyy _].
        rewrite /at_key /hist_at_key in Hatkey.
        rewrite !filter_app in Hatkey.
        rewrite Hatkey_hfyy in Hatkey.
        rewrite right_id in Hatkey.
        rewrite Hatkey_hby in Hatkey.
        rewrite Hatkey_hfxy in Hatkey.
        rewrite filter_cons_False in Hatkey; [|by rewrite Hkey_x].
        rewrite filter_cons_True in Hatkey; [|by rewrite Hkey_y].
        simpl in *.
        by simplify_eq.
      - rewrite -Hatkey_y.
        iMod (OwnMemKey_obs_frame_prefix with "HGinv [$Hy $Hobs]")
          as "[Hy %Heq]"; [solve_ndisj|done|].
        rewrite -Heq in Hatkey.
        rewrite Hatkey in Hatkey_y.
        iModIntro.
        iFrame "Hy".
        iPureIntro.
        by simplify_eq. }
    iMod ("H" with "Hy") as (->) "Hy".
    iClear "H".

    assert (∃ ao : option we,
                at_key "x" h' = ao ∧
                ((vo = InjLV #() ∧ ao = None) ∨
                 (∃ a : we, vo = InjRV (we_val a) ∧ ao = Some a)))
      as [a [Hatkey_a Hdisj']].
    { destruct Hdisj as [Hdisj | Hdisj].
      - destruct Hdisj as [-> Hdisj]. exists None. split; [done|]. left. done.
      - destruct Hdisj as [a [-> Hdisj]]. exists (Some a). split; [done|].
        by eauto. }

    iAssert ("x" ↦ₖ Some we_x ={⊤ ∖ ↑Ny}=∗ ⌜a = Some we_x⌝ ∗ "x" ↦ₖ Some we_x)%I
      as "H".
    { iMod (Obs_compare with "HGinv Hobs' Hobs''") as %Hprefix'; [solve_ndisj|].
      iIntros "Hx".
      destruct Hprefix' as [Hprefix'|Hprefix'].
      - (* `h'` is at least `h`, and `h` is at least
             `hb ++ [we_x] ++ hfx ++ [we_y]`,
              thus `at_key "x" h'` can only be we_x *)
        admit.
      - rewrite -Hatkey_x.
        iMod (OwnMemKey_obs_frame_prefix with "HGinv [$Hx $Hobs']")
          as "[Hy %Heq]"; [solve_ndisj|done|].
        rewrite -Heq in Hatkey_a.
        rewrite Hatkey_a in Hatkey_x.
        iModIntro.
        iFrame "Hy".
        iPureIntro.
        by simplify_eq. }
    iMod ("H" with "Hx") as (->) "Hx".
    iClear "H".

    destruct Hdisj' as [[_ Hineq]|Hdisj']; [done|].
    destruct Hdisj' as [a [-> Heq]].
    assert (we_x = a) as <-.
    { by inversion Heq. }
    iMod ("Hclose" with "[Hx Hy]") as "_".
    { iRight. iExists _, _, _, _, _. iFrame "Hx Hy #".
      eauto. }
    iModIntro.
    do 2 wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    rewrite Hval.
    iSplit; [done|].
    by iApply "HΦ".
  Admitted.

  Lemma proof_of_node0 (clt_00 : socket_address) A :
    DB_addr ∈ A →
    clt_00 ∉ A →
    GlobalInv -∗
    fixed A -∗
    (∀ A ca, init_client_proxy_leader_spec A ca leader_si) -∗
    Obs DB_addr [] -∗
    inv Ny inv_def -∗
    {{{ free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        db_sa ⤇ leader_si ∗
        "x" ↦ₖ None }}}
      node0 #clt_00 #db_sa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HInDB HnInA) "#HGinv #Hfixed #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hfps & Hclt00 & #Hsi & Hx) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[//] [//] [$Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (wr rd) "[_ Hwr]".
    wp_pures.
    iApply (wp_do_writes with "[$] [$] [$] [$] Hx HΦ").
  Qed.

  Lemma proof_of_node1 (clt_01 : socket_address) A :
    DB_addrF ∈ A →
    clt_01 ∉ A →
    GlobalInv -∗
    fixed A -∗
    (∀ A ca, init_client_proxy_follower_spec A ca DB_addrF follower_si) -∗
    Obs DB_addr [] -∗
    inv Ny inv_def -∗
    {{{ free_ports (ip_of_address clt_01) {[port_of_address clt_01]} ∗
        clt_01 ⤳ (∅, ∅) ∗
        DB_addrF ⤇ follower_si ∗
        "x" ↦ₖ None }}}
      node1 #clt_01 #db_Fsa @[ip_of_address clt_01]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HInDB HnInA) "#HGinv #Hfixed #Hspec #Hobs #Hinv_y".
    iIntros "!>" (Φ) "(Hfps & Hclt00 & #Hsi & Hx) HΦ".
    wp_lam.
    wp_pures.
    wp_apply ("Hspec" with "[//] [//] [$Hfps $Hclt00]"); [by iFrame "#"|].
    iIntros (rd) "[#Hobs' #Hrd]".
    wp_pures.
    by iApply wp_do_reads.
  Qed.

End proof_of_code.
*)

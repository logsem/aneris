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

  Definition read_spec_atomic (rd : val) (sa : socket_address) : iProp Σ :=
    ∀ (E : coPset) (k : Key),
    ⌜↑DB_InvName ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h : ghst) (q : Qp) (a_old : option we),
            ⌜at_key k h = a_old⌝ ∗
            Obs DB_addr h ∗
            k ↦ₖ{q} a_old >>>
      rd #k @[ip_of_address sa] E
    <<<▷ RET match a_old with None => NONEV | Some a => SOMEV (we_val a) end;
         (⌜a_old = None⌝ ∗ k ↦ₖ{q} None) ∨
         (∃ e, ⌜a_old = Some e⌝ ∗
            (k ↦ₖ{q} Some e)) >>>.

End API_spec_ext.

Section proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si : message → iProp Σ).
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

  Definition inv_x (γ : gname) (a : we) : iProp Σ :=
    ("x" ↦ₖ Some a ∗ ⌜we_val a = #37⌝) ∨ token γ.

  Definition inv_y (γ : gname) : iProp Σ :=
    ∃ h owe, Obs DB_addr h ∗ ⌜at_key "y" h = owe⌝ ∗ "y" ↦ₖ owe ∗
             ∀ a, (⌜owe = Some a ∧ we_val a = (# 1)⌝) →
                  (∃ a', ⌜a' <ₜ a⌝ ∗ inv Nx (inv_x γ a')).

  (* TODO: Get empty history from nothing. *)
  Lemma wp_do_writes wr clt_00 γ :
    GlobalInv -∗
    inv Ny (inv_y γ) -∗
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
    iMod (inv_alloc Nx _ (inv_x γ a) with "[Hx]") as "#HIx".
    { iModIntro. iLeft. eauto with iFrame. }
    wp_apply ("Hawr" $! (⊤ ∖ ↑Ny) _ (SerVal #1)); [solve_ndisj|done|].
    iInv Ny as "IH" "Hclose".
    iDestruct "IH" as (h' owe) "(#>Hobs'' & >%Hatkey' & >Hy & _)".
    iMod (Obs_compare with "HGinv Hobs' Hobs''") as %Hprefix; [solve_ndisj|].
    iAssert (∃ hmax, ⌜(h ++ [a]) `prefix_of` hmax⌝ ∗
                     ⌜h' `prefix_of` hmax⌝ ∗
                     Obs DB_addr hmax)%I
      as (hmax Hhmax1 Hhmax2) "Hobs'''".
    { destruct Hprefix as [Hprefix | Hprefix].
      - by iExists _; iFrame "Hobs''".
      - by iExists _; iFrame "Hobs'". }
    rewrite -Hatkey'.
    iMod (OwnMemKey_obs_frame_prefix with "HGinv [$Hy $Hobs''']")
      as "[Hy %Hatkey'']"; [solve_ndisj|done|].
    rewrite Hatkey'.
    iModIntro.
    iExists hmax, owe.
    rewrite -Hatkey''.
    iFrame "#∗".
    iSplit; [done|].
    iNext.
    iIntros (h'' a').
    iDestruct 1 as (Hatkey''' Hkey' Hval' Hle) "[Hy Hobs'''']".
    simpl in *.
    iMod ("Hclose" with "[-HΦ]"); [|by iApply "HΦ"].
    iNext.
    iExists (hmax ++ h'' ++ [a']), (Some a'). iFrame.
    iSplit; [|].
    { iPureIntro.
      rewrite /at_key !assoc hist_at_key_add_r_singleton; [|done].
      apply last_snoc. }
    iIntros (a'' [Heq Heq']).
    simplify_eq.
    iExists a.
    iFrame "#".
    iPureIntro.
    apply Hle.
    eapply elem_of_prefix; [|apply Hhmax1].
    set_solver.
  Qed.

  Lemma wp_wait_on_read clt_00 clt_01 γ rd :
    ip_of_address clt_00 = ip_of_address clt_01 →
    GlobalInv -∗
    read_spec_atomic rd clt_01 -∗
    {{{ inv Ny (inv_y γ) }}}
      wait_on_read rd #"y" #1 @[ip_of_address clt_00]
    {{{ a, RET #(); inv Nx (inv_x γ a) }}}.
  Proof.
    iIntros (Hip) "#HGinv #Hard".
    iIntros "!>" (Φ) "#Hinv HΦ".
    wp_lam.
    wp_pures.
    iLöb as "IH".
    wp_bind (rd _).
    rewrite Hip.
    wp_apply ("Hard" $! (⊤∖↑Ny)); [solve_ndisj|done|].
    iInv Ny as "HI" "Hclose".
    iDestruct "HI" as (h owe) "(#>Hobs & >%Hatkey & >Hy & #Himpl)".
    iModIntro.
    iExists h, _, owe.
    iFrame "#∗".
    iSplit; [done|].
    iIntros "!> [H|H]".
    { iDestruct "H" as (->) "Hy".
      iMod ("Hclose" with "[-HΦ]").
      { iIntros "!>". iExists _, _. iFrame "#∗". done. }
      iModIntro.
      wp_pures.
      by iApply "IH". }
    iDestruct "H" as (e ->) "Hy".
    iMod ("Hclose" with "[-HΦ]").
    { iIntros "!>". iExists _, _. iFrame "#∗". done. }
    iModIntro.
    wp_pures.
    case_bool_decide as Heq.
    - wp_pures.
      iDestruct ("Himpl" with "[]") as (a) "[_ H]".
      { by simplify_eq. }
      by iApply "HΦ".
    - wp_pures.
      by iApply "IH".
  Qed.

  Lemma wp_do_reads clt_00 clt_01 γ rd :
    ip_of_address clt_00 = ip_of_address clt_01 →
    GlobalInv -∗
    read_spec_atomic rd clt_01 -∗
    inv Ny (inv_y γ) -∗
    {{{ token γ }}}
      do_reads rd @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hip) "#HGinv #Hard #Hinvy".
    iIntros "!>" (Φ) "Htok HΦ".
    wp_lam.
    wp_apply (wp_wait_on_read); [done..|].
    iIntros (a) "#Hinvx".
    wp_pures.
    rewrite Hip.
    wp_apply ("Hard" $! (⊤∖↑Nx)); [solve_ndisj|done|].
    iInv Nx as "HI" "Hclose".
    iDestruct "HI" as "[>[Hx %Hval]|>HI]"; last first.
    { iDestruct (token_exclusive with "Htok HI") as "[]". }
    iMod (OwnMemKey_some_obs_we with "HGinv Hx") as "[Hx H]"; [solve_ndisj|].
    iDestruct "H" as (h) "[#Hobs %Hatkey]".
    iModIntro.
    iExists _, _, _.
    iFrame "#∗".
    iSplit; [done|].
    iIntros "!> [[%Heq _]|H]"; [done|].
    iDestruct "H" as (e) "[%Heq Hx]".
    simplify_eq.
    iMod ("Hclose" with "[Htok]").
    { by iRight. }
    iModIntro.
    do 2 wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    rewrite Hval.
    iSplit; [done|].
    by iApply "HΦ".
  Qed.

End proof_of_code.

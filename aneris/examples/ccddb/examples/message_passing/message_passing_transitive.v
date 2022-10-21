From iris.algebra Require Import csum excl frac auth.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb Require Import spec spec_util.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.aneris_lang Require Import lifting lang network tactics proofmode.

Section resources.
  Context `{!DB_time, !DB_events}.

  Definition oneshotR := csumR (exclR unitR) (agreeR (leibnizO we)).
  Definition gmemCmra : cmra := prodR fracR (agreeR (leibnizO gmem)).

  Class mpG Σ `{!DB_time, !DB_events} := MpG {
    mp_tokG :> inG Σ (exclR unitO);
    mp_gmem :> inG Σ gmemCmra;
    oneshot_inG :> inG Σ oneshotR;

    mp_token1_name : gname;
    mp_ghst_name : gname;
  }.

  Class mpPreG Σ `{!DB_time, !DB_events} := MpPreG {
    mpPre_tokG :> inG Σ (exclR unitO);
    mpPre_gmem :> inG Σ gmemCmra;
    mpPre_oneS :> inG Σ oneshotR;
  }.

  Definition mpΣ  : gFunctors :=
    #[GFunctor (exclR unitO); GFunctor gmemCmra; GFunctor oneshotR].

  Instance subG_mpPre {Σ} : subG mpΣ Σ → mpPreG Σ.
  Proof. solve_inG. Qed.

End resources.

Section resources_lemmas.
  Context `{!DB_time, !DB_events, !mpG Σ}.

  Definition pending γ := own γ (Cinl (Excl ())).
  Definition shot γ a := own γ (Cinr (to_agree a)).
  Lemma new_pending : ⊢ |==> ∃ γ, pending γ.
  Proof. by apply own_alloc. Qed.
  Lemma shoot γ a : pending γ ==∗ shot γ a.
  Proof.
    apply own_update.
    intros n [f |]; simpl; eauto.
    destruct f; simpl; try by inversion 1.
  Qed.
  Lemma shot_agree γ a b:
    shot γ a -∗ shot γ b -∗ ⌜a = b⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -Cinr_op csum_validI. iDestruct "H" as %?.
    iIntros "!%". by apply (to_agree_op_inv_L (A:=leibnizO we)).
  Qed.

  Lemma shot_not_pending γ a :
    shot γ a -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp". iDestruct (own_valid_2 with "Hs Hp") as %[].
  Qed.

  Definition token γ : iProp Σ := own γ (Excl ()).

  Lemma token_exclusive γ :
    token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Definition ownGhst (q : Qp) (h : gmem) :=
    own (A := gmemCmra) mp_ghst_name (q, to_agree h).

  Lemma ownGhst_agree p q h1 h2:
    ownGhst p h1 -∗ ownGhst q h2 -∗ ⌜h1 = h2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "H") as %HValid.
    destruct HValid as [_ ?]. simpl in *.
    iIntros "!%". by apply (to_agree_op_inv_L (A:=leibnizO gmem)).
  Qed.

  Lemma ownGhst_update h1 h2 :
    ownGhst (1/2) h1 -∗ ownGhst (1/2) h1
    ==∗ ownGhst (1/2) h2 ∗ ownGhst (1/2) h2.
  Proof.
    iIntros "H1 H2". rewrite /ownGhst. iCombine "H1 H2" as "H".
    rewrite -own_op -pair_op frac_op  Qp.half_half agree_idemp.
    iApply (own_update with "H"). apply cmra_update_exclusive.
    rewrite -pair_op frac_op Qp.half_half agree_idemp //.
  Qed.

End resources_lemmas.

Section example.
  Context `{!anerisG Mdl Σ}.
  Context (z0 z1 z2 : socket_address).
  Context (Hzeq12 : z0 ≠ z1) (Hzeq23 : z1 ≠ z2) (Hzeq13 : z2 ≠ z0).

  Program Instance myparams : DB_params :=
    {| DB_addresses := [z0; z1; z2];
       DB_keys := {["x"; "y"]};
       DB_InvName := nroot .@ "dbinv";
       DB_serialization := int_serialization;
    |}.
  Next Obligation.
    repeat constructor; set_solver.
  Qed.

  Context `{!DB_time, !DB_events,
            !DB_resources Mdl Σ, !Maximals_Computing,
            !DB_init_function, !DB_init, !mpG Σ}.

  Definition z0_prog : expr := λ: "wr",
    "wr" #"x" #0;;
    "wr" #"x" #37.

  Definition z1_prog : expr := λ: "rd" "wr",
    repeat_read_until "rd" #"x" #37;;
    "wr" #"y" #1.

  Definition z2_prog : expr := λ: "rd",
    repeat_read_until "rd" #"y" #1;;
    "rd" #"x".

  Definition Nx := nroot.@"x".
  Definition Ny := nroot.@"y".

  Local Notation "k ↦ᵤ{ q } h" := (k ↦ᵤ h ∗ ownGhst q h)%I
  (at level 20, q at level 50, format "k  ↦ᵤ{ q }  h") : bi_scope.

  Definition inv_x γ1 γ2 : iProp Σ :=
    ∃ h, "x" ↦ᵤ{1/2} h ∗
       ((pending γ1 ∗ ⌜∀ a, a ∈ h → WE_val a ≠ #37⌝)
        ∨ (token γ2 ∗ ∃ a, shot γ1 a ∗ ⌜WE_val a = #37 ∧ Maximum h = Some a⌝ ∗
                                       ⌜∀ a', a' ∈ h → WE_val a' = #37 → a = a'⌝)).

  Definition inv_y γ1 : iProp Σ :=
    ∃ h, "y" ↦ᵤ h ∗ ∀ a, ⌜a ∈ h ∧ WE_val a = #1⌝ →
                         ∃ a', ⌜a' <ₜ a⌝ ∗ shot γ1 a'.

  Opaque ip_of_address.

  Lemma z0_spec γ1 γ2 h s wr :
    h ⊆ erasure_set s →
    GlobalInv -∗
    write_spec wr 0 z0 -∗
    {{{ Seen 0 s ∗ ownGhst (1/2) h ∗ token γ2 ∗ inv Nx (inv_x γ1 γ2) }}}
      z0_prog wr @[ip_of_address z0]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "% #HIG #Hwr !#" (Φ) "(#Hs & Hghst & Htok1 & #HIx) HΦ".
    wp_pures. wp_bind (wr _ _).
    set (P := (ownGhst (1/2) h ∗ token γ2)%I).
    set (Q := (λ (_ : ae) (_ : gmem) (_ : lhst), ∃ h' s',
           Seen 0 s' ∗ ownGhst (1/2) h' ∗ token γ2 ∗ ⌜h' ⊆ erasure_set s'⌝)%I).
    wp_apply ("Hwr" $! (⊤ ∖ ↑Nx) _ (SerVal #0) _ P Q
                with "[] [] [] [$Hghst $Htok1 $Hs]");
      [done|solve_ndisj| |done|].
    { iIntros "!#" (s1 e) "% % % %Hval_e (Hghst & Htok1)". rewrite /P /Q.
      iInv (Nx) as (h') ">[[Hxu Hghst'] [[Hpend %Hn37] | [Htok1' H]]]" "Hclose";
        last first.
      { iDestruct (own_valid_2 with "Htok1 Htok1'") as %[]%exclusive_r. }
      iIntros "!#" (h2) "% % % Hs1 Hxs".
      iDestruct (ownGhst_agree with "Hghst Hghst'") as %<-.
      iMod (ownGhst_update _ (h ∪ {[erasure e]}) with "Hghst Hghst'")
        as "[Hghst Hghst']".
      iDestruct (User_Sys_agree with "Hxu Hxs") as %<-.
      iMod (OwnMem_update _ _ (h ∪ {[erasure e]})
              with "Hxu Hxs") as "[Hxu Hxs]"; first set_solver.
      iModIntro. iFrame "Hxs".
      iMod ("Hclose" with "[Hxu Hpend Hghst']") as "_".
      { iModIntro. iExists _. iFrame. iLeft. iFrame. iPureIntro.
        intros a' [? | ->%elem_of_singleton]%elem_of_union; [by apply Hn37|].
        rewrite erasure_val Hval_e //. }
      iModIntro. iExists (_ ∪ _), _. iFrame. iPureIntro.
      apply union_singleton_erasure_set. set_solver. }
    rewrite /P /Q. clear P Q.
    iDestruct 1 as (???) "(% & Hx)".
    iDestruct "Hx" as (h1 s2) "(#Hs1 & Hghst & Htok1 & %) /=".
    wp_seq.
    set (P := (ownGhst (1/2) h1 ∗ token γ2)%I).
    set (Q := (λ (_ : ae) (_ : gmem) (_ : lhst), True : iProp Σ)%I).
    wp_apply ("Hwr" $! (⊤ ∖ ↑Nx) _ (SerVal #37) _ P Q
                with "[] [] [] [$Hghst $Htok1 $Hs1]");
      [done|solve_ndisj| |done|].
    { iIntros "!#" (s3 e') "% % % %Hval_e (Hghst & Htok1)".
      iInv (Nx) as (h') ">[[Hxu Hghst'] [[Hpend %Hn37] | [Htok1' H]]]" "Hclose";
        last first.
      { iDestruct (own_valid_2 with "Htok1 Htok1'") as %[]%exclusive_r. }
      iIntros "!#" (h2) "% % % #Hs2 Hxs".
      iDestruct (ownGhst_agree with "Hghst Hghst'") as %<-.
      iDestruct (User_Sys_agree with "Hxu Hxs") as %<-.
      iMod (ownGhst_update _ (h1 ∪ {[erasure e']}) with "Hghst Hghst'")
        as "[Hghst Hghst']".
      iMod (OwnMem_update _ _ (h1 ∪ {[erasure e']})
              with "Hxu Hxs") as "[Hxu Hxs]"; first set_solver.
      iModIntro. iFrame.
      iMod (Maximum_ghst _ _ e' with "HIG Hs2 Hxu") as "[%Hmax_h' Hxu]";
        [solve_ndisj| |set_solver|done|].
      { apply union_singleton_erasure_set. set_solver. }
      iMod (shoot _ (erasure e') with "Hpend") as "Hshot".
      iMod ("Hclose" with "[-]") as "_"; [| by iModIntro].
      iModIntro. iExists _. iFrame. iRight. iFrame.
      iExists _. iFrame. iPureIntro.
      split; [rewrite erasure_val //|].
      intros ? [Hin | ->%elem_of_singleton]%elem_of_union ?; [|done].
      by destruct (Hn37 _ Hin). }
    iIntros "_". by iApply "HΦ".
  Qed.

  Theorem z1_spec γ1 γ2 s rd wr :
    GlobalInv -∗
    read_spec rd 1 z1 -∗
    write_spec wr 1 z1 -∗
    {{{ Seen 1 s ∗ inv Nx (inv_x γ1 γ2) ∗ inv Ny (inv_y γ1) }}}
      z1_prog rd wr @[ip_of_address z1]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#HIG #Hrd #Hwr !#" (Φ) "(#Hs & #HIx & #HIy) HΦ".
    wp_pures. wp_bind (repeat_read_until _ _ _).
    wp_apply (repeat_read_until_spec with "[] Hs");
      [done|done|].
    iIntros (s2 ex) "(% & Hs2 & %Hval_e & %Hmaxi_e & #Hsnap & %) /=".
    iApply fupd_aneris_wp.
    iInv Nx as ">H" "Hcl".
    iDestruct "H" as (h) "[Hxu H]".
    iDestruct "Hxu" as "[Hxu Hgx]".
    iMod (OwnMemSnapshot_included with "HIG Hxu Hsnap") as "[Hxu %Hincl]";
      first solve_ndisj.
    assert (erasure ex ∈ h) as Hin_e by set_solver.
    iCombine "Hxu" "Hgx" as "Hxu".
    iAssert (⌜∀ a : we, a ∈ h → WE_val a ≠ #37⌝
               ∨ ∃ a, shot γ1 a ∗ ⌜WE_val a = #37 ∧ Maximum h = Some a⌝
                      ∗ ⌜∀ a', a' ∈ h → WE_val a' = #37 → a = a'⌝)%I
            with "[H]" as "#[%Hn37 | H37]".
    { iDestruct "H" as "[[Hpend %Hn37] | [Htok1' H]]"; auto. }
    { destruct (Hn37 _ Hin_e). rewrite erasure_val //. }
    iDestruct "H37" as (a) "(#Hshot & [% %] & %Huniq)".
    rewrite -erasure_val in Hval_e.
    destruct (elem_of_Maximals_restrict_key _ _ _ Hmaxi_e).
    rewrite (Huniq (erasure ex)) //.
    iMod ("Hcl" with "[Hxu H]") as "_".
    { iNext; iExists _; iFrame. }
    iModIntro.
    wp_seq.
    set (P := True%I : iProp Σ).
    set (Q := (λ (_ : ae) (_ : gmem) (_ : lhst), True : iProp Σ)%I).
    wp_apply ("Hwr" $! (⊤ ∖ ↑Ny) _ (SerVal #1) _ P Q
                with "[] [] [] [$Hs2]");
      [done|solve_ndisj| |done|].
    { iIntros "!#" (s3 ey) "% % % %Hval_e2 _".
      iInv Ny as (hy) "(>Hyu & #Hhy)" "Hclose".
      iIntros "!# %h3 % % % #Hs3 Hys".
      iDestruct (User_Sys_agree with "Hyu Hys") as %<-.
      iMod (OwnMem_update _ _ (hy ∪ {[erasure ey]})
              with "Hyu Hys") as "[Hyu Hys]"; first set_solver.
      iModIntro. iFrame.
      iMod (Maximum_lhst_gt ex ey  with "HIG Hs3") as %Hneq;
        [solve_ndisj|by eapply ae_key_neq |set_solver|done|].
      iMod ("Hclose" with "[-]"); [|by iModIntro].
      iExists (_ ∪ _). iFrame.
      iIntros "!#" (e').
      iIntros ([[? | ->%elem_of_singleton]%elem_of_union ?]);
        first by iApply "Hhy".
      iExists _. iFrame "% #". }
    iIntros "_". by iApply "HΦ".
  Qed.

  Theorem z2_spec γ1 γ2 s rd :
    GlobalInv -∗
    read_spec rd 2 z2 -∗
    {{{ Seen 2 s ∗ inv Ny (inv_y γ1) ∗ inv Nx (inv_x γ1 γ2) }}}
      z2_prog rd @[ip_of_address z2]
    {{{ RET (InjRV #37); True }}}.
  Proof.
    iIntros "#HIG #Hrd !#" (Φ) "(#Hs & #HIx & #HIy) HΦ".
    wp_pures. wp_bind (repeat_read_until _ _ _).
    wp_apply (repeat_read_until_spec with "[] Hs");
      [done|done|].
    iIntros (s2 e) "(% & Hs2 & % & % & #Hsnap & %) /=".
    iApply fupd_aneris_wp.
    iInv Ny as (hy) "(>Hyu & #Hhy)" "Hclose".
    iMod (OwnMemSnapshot_included with "HIG Hyu Hsnap") as "[Hyu %Hincl]";
      first solve_ndisj.
    iMod ("Hclose" with "[Hyu Hhy]") as "_".
    { iModIntro. iExists _. iFrame. iFrame "#". }
    iModIntro.
    assert (erasure e ∈ hy) as Hin_e by set_solver.
    assert (e ∈ s2).
    { by eapply elem_of_Maximals_restrict_key. }
    wp_seq.
    iApply aneris_wp_fupd.
    iDestruct ("Hhy" $! (erasure e) with "[]") as (a) "[% #Hshot]".
    { iPureIntro; rewrite erasure_val //. }
    wp_apply ("Hrd" with "[//] Hs2").
    iIntros (w) "Hw".
    iDestruct "Hw" as (s3 Hs3) "[#Hs3 [[-> %Hx]|Hw]]".
    - iInv (Nx) as (h') ">[[Hxu Hghst'] [[Hpend %Hn37] | [Htok1 H]]]" "Hclose".
      { iDestruct (shot_not_pending with "Hshot Hpend") as %[]. }
      iDestruct "H" as (a') "(#Hshot' & [% %] & %Huniq)".
      iDestruct (shot_agree with "Hshot Hshot'") as %<-.
      iMod (Maximum_causality e _ with "HIG Hs3 Hxu") as ([? [? ?]]) "Hxu";
        [solve_ndisj|set_solver|by rewrite -erasure_time|done|].
      set_solver.
    - iDestruct "Hw" as (v e') "(-> & <- & %He'1 & Hxe' & %He'2)".
      iInv (Nx) as (h') ">[[Hxu Hghst'] [[Hpend %Hn37] | [Htok1 H]]]" "Hclose".
      { iDestruct (shot_not_pending with "Hshot Hpend") as %[]. }
      iDestruct "H" as (a') "(#Hshot' & [%Hval %] & %Huniq)".
      iDestruct (shot_agree with "Hshot Hshot'") as %<-.
      iMod (Maximum_elem_of_ghst with "HIG Hxu") as "[% Hxu]";
        [solve_ndisj|done|].
      iMod (Causality_2 e a with "HIG Hs3 Hxu") as ([e'' [? <-]]) "Hxu";
        [solve_ndisj|set_solver|done|by rewrite -erasure_time|].
      iMod (OwnMemSnapshot_included with "HIG Hxu Hxe'") as "[Hxu %Hincl']";
      first solve_ndisj.
      iMod (Maximum_maximals_val_agree with "HIG Hs3 Hxu") as "[%Heq Hxu]";
          [solve_ndisj|done|done|done|set_solver|].
      iMod ("Hclose" with "[- HΦ]") as "_".
      { iModIntro. iExists _. iFrame. iRight.
        iFrame. iExists _. by iFrame "% #". }
      rewrite -Heq -erasure_val Hval.
      iModIntro.
      iApply "HΦ"; done.
  Qed.

End example.

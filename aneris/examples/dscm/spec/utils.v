From iris.proofmode Require Import proofmode.
From aneris.examples.dscm.spec Require Import resources stdpp_utils events.

Section with_Σ.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events, !DB_resources Mdl Σ}.

  (* TODO: maybe add frame after [we1] here *)
  Lemma OwnMemKey_Obs_extend E h k we1 we2 :
    nclose DB_InvName ⊆ E →
    WE_key we1 = WE_key we2 →
    we1 ≠ we2 →
    GlobalInv -∗
    Obs (h ++ [we1]) -∗
    k ↦ₖ Some (mval_of_we we2) ={E}=∗
    k ↦ₖ Some (mval_of_we we2) ∗
    ∃ hf, Obs (h ++ [we1] ++ hf ++ [we2]).
  Proof.
    iIntros (HE Heq Hneq) "#HGinv #Hobs Hk".
    iMod (OwnMemKey_key with "Hk") as "[Hk %Hkey]"; [solve_ndisj|].
    iMod (OwnMemKey_some_obs_we with "Hk") as "[Hk (%h' & #Hobs' & %Hatkey)]";
      [solve_ndisj|].
    iMod (Obs_compare with "HGinv Hobs Hobs'") as %Hle; [solve_ndisj|].
    destruct Hle as [Hle | Hle]; last first.
    { (* Solve contradiction *)
      iMod (OwnMemKey_obs_frame_prefix_some with "[$Hk $Hobs]")
        as "[Hk %Hatkey']"; [solve_ndisj|done..|].
      rewrite at_key_snoc_some in Hatkey'; naive_solver. }
    assert (Some (mval_of_we we2) = mval_of_we_opt (at_key k h')) as ->.
    { by rewrite Hatkey. }
    iMod (OwnMemKey_allocated with "Hk") as "(%we' & Hk & %Hatkey' & %Hle')";
      [solve_ndisj|done|apply at_key_snoc_some; naive_solver|].
    assert (we' = we2) as -> by naive_solver. clear Hatkey'.
    iFrame "Hk".
    destruct Hle as [h'' ->].
    rewrite /at_key /hist_at_key in Hatkey.
    rewrite !filter_app in Hatkey.
    rewrite filter_cons_True in Hatkey; [|naive_solver].
    rewrite -app_assoc in Hatkey.
    rewrite last_app_cons in Hatkey.
    apply last_cons_ne in Hatkey; [|done].
    apply last_filter_postfix in Hatkey.
    destruct Hatkey as (yz & zs & -> & HP).
    iMod (Obs_get_smaller with "Hobs'") as "Hobs''"; [solve_ndisj| |].
    { rewrite !app_assoc. apply prefix_app_r. rewrite -!app_assoc. done. }
    by eauto.
  Qed.

  (* TODO: Nice lemma, but not used. Keep? *)
  Lemma Writes_obs_elem_of E we h sa s :
    nclose DB_InvName ⊆ E →
    at_origin sa h = Some we →
    Obs h -∗ Writes sa s ={E}=∗
    Writes sa s ∗ ⌜we ∈ s⌝.
  Proof.
    iIntros (HE Hatorigin) "Hobs Hwrites".
    iMod (Writes_obs_at_origin with "[$Hwrites $Hobs]")
      as "[Hwrites %Hhistatorigin]".
    iFrame "Hwrites".
    iModIntro. iPureIntro.
    pose proof (at_origin_hist_at_origin_inv sa h we Hatorigin) as Hsplit.
    destruct Hsplit as (ys & zs & -> & _).
    assert (we ∈ hist_at_origin sa (ys ++ [we] ++ zs)) as Hin.
    { rewrite /hist_at_origin.
      rewrite filter_app.
      apply elem_of_app.
      right.
      rewrite filter_cons_True; [|by eapply at_origin_has_origin].
      apply elem_of_cons. by left. }
    eapply elem_of_list_lookup in Hin.
    destruct Hin as [i Hin].
    eapply elem_of_list_lookup_2.
    eapply prefix_lookup_Some; [|done].
    apply Hin.
  Qed.

  Lemma OwnMemKey_origin_in_Writes E k q we sa s :
    nclose DB_InvName ⊆ E →
    WE_key we = k →
    WE_origin we = sa →
    k ↦ₖ{ q } Some (mval_of_we we) -∗ Writes sa s ={E}=∗
    k ↦ₖ{ q } Some (mval_of_we we) ∗ Writes sa s ∗ ⌜we ∈ s⌝.
  Proof.
    iIntros (HE Hkey Horig) "Hk Hwrites".
    iMod (OwnMemKey_some_obs_we with "Hk") as
      "[Hk (%h & #Hobs & %Hatkey)]"; [solve_ndisj|].
    iMod (Writes_obs_at_origin with "[$Hwrites $Hobs]")
      as "[Hwrites %Hatorigin]".
    iModIntro. iFrame. iPureIntro.
    pose proof (at_key_hist_at_key_inv k h we Hatkey) as Hsplit.
    destruct Hsplit as [ys [zs [-> _]]].
    assert (we ∈ hist_at_origin sa (ys ++ [we] ++ zs)) as Hin.
    { rewrite /hist_at_origin filter_app.
      apply elem_of_app. right.
      rewrite filter_cons_True; [|done].
      apply elem_of_cons. by left. }
    by eapply elem_of_prefix.
  Qed.

  (* Implication of potential strict total order property of [Obs h] *)
  Lemma Obs_unique E xs we ys :
    nclose DB_InvName ⊆ E →
    Obs (xs ++ [we] ++ ys) ={E}=∗ ⌜we ∉ xs⌝ ∗ ⌜we ∉ ys⌝.
  Proof.
    iIntros (HE) "Hobs".
    iMod (Obs_snoc_time with "Hobs") as %[Hle1 Hle2]; [solve_ndisj|].
    iModIntro. iFrame. iPureIntro.
    split.
    - intros Hin. specialize (Hle1 we Hin). by apply strict_ne in Hle1.
    - intros Hin. specialize (Hle2 we Hin). by apply strict_ne in Hle2.
  Qed.

  (* Implication of potential strict total order property of [Writes h] *)
  Lemma Writes_unique E sa xs we ys :
    nclose DB_InvName ⊆ E →
    Writes sa (xs ++ [we] ++ ys) ={E}=∗
    Writes sa (xs ++ [we] ++ ys) ∗ ⌜we ∉ xs⌝ ∗ ⌜we ∉ ys⌝.
  Proof.
    iIntros (HE) "Hwrites".
    iDestruct (Writes_obs_exists with "Hwrites") as (h) "[#Hobs %Hle]".
    apply sublist_of_split in Hle.
    destruct Hle as (xs' & ys' & -> & Hxs' & Hys').
    iMod (Obs_unique with "Hobs") as %[Hin1 Hin2]; [solve_ndisj|].
    iFrame. iModIntro. iPureIntro.
    split.
    - intros Hin. apply Hin1. by eapply elem_of_sublist.
    - intros Hin. apply Hin2. by eapply elem_of_sublist.
  Qed.

  Lemma Writes_Obs_origin_frame E s we sa h hf :
    nclose DB_InvName ⊆ E →
    Writes sa (s ++ [we]) -∗ Obs (h ++ [we] ++ hf) ={E}=∗
    Writes sa (s ++ [we]) ∗ ⌜hist_at_origin sa hf = []⌝.
  Proof.
    iIntros (HE) "HWrites #HObs".
    iMod (Writes_obs_at_origin with "[$HWrites $HObs]") as "[HWrites %Hle]".
    rewrite /hist_at_origin in Hle.
    rewrite /hist_at_origin.
    rewrite !filter_app in Hle.
    iDestruct (Writes_origin with "HWrites") as %Horig.
    rewrite filter_cons_True in Hle; [| by apply Horig; set_solver ].
    iMod (Writes_unique with "HWrites") as "[Hwrites [%Hwe1 _]]"; [solve_ndisj|].
    iMod (Obs_unique with "HObs") as %[Hwe2' _]; [solve_ndisj|].
    assert (we ∉ filter (λ x : events.we, WE_origin x = sa) h) as Hwe2.
    { intros Hin. apply Hwe2'.
      eapply elem_of_sublist; [done|apply sublist_filter]. }
    assert ((filter (λ x : events.we, WE_origin x = sa) h) = s) as Heq.
    { eapply (prefix_sync_eq); [done|done|apply Hle]. }
    rewrite Heq in Hle.
    apply prefix_app_inv, prefix_cons_inv_2 in Hle.
    iModIntro. iFrame "Hwrites". iPureIntro.
    by apply prefix_nil_inv.
  Qed.

End with_Σ.

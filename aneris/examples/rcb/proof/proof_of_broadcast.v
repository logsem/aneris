(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list_proof map_proof queue_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.rcb Require Import rcb_code.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import
     model_lst model_gst model_update_system model_update_lst model_update_gst.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.rcb.util Require Import list_proof_alt.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.
  Context (γGown γGsnap : gname) (γLs : list gname).

  Definition internal_broadcast_spec
             (broadcast : val) (i: nat) (z : socket_address) : iProp Σ :=
    ∀ (v : SerializableVal),
    ⌜RCB_addresses !! i = Some z⌝ -∗
    <<< ∀∀ (h : gset global_event) (s : gset local_event),
          own_global_user γGown γGsnap h ∗
          lhst_user γLs i s >>>
          broadcast v @[ip_of_address z] ↑RCB_InvName
    <<<▷ ∃∃ (w : val) (a : local_event),
          RET w;
            ⌜is_lev w a⌝ ∗
            let s' := s ∪ {[ a ]} in
            ⌜a ∉ s⌝ ∗
            let e := erase a in
            ⌜e ∉ h⌝ ∗
            ⌜a.(le_payload) = v⌝ ∗
            ⌜a.(le_orig) = i⌝ ∗
            let h' := h ∪ {[ e ]} in
            ⌜e ∈ compute_maximals ge_time h'⌝ ∗
            ⌜compute_maximum le_time s' = Some a⌝ ∗
            own_global_user γGown γGsnap h' ∗
            lhst_user γLs i s' >>>.


  Lemma broadcast_ghost_update i t Su Sl h v :
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := Su |} ->
    Global_Inv γGown γGsnap γLs  ⊢
    own_global_user γGown γGsnap h -∗
    lhst_user γLs i Su -∗
    lhst_lock γLs i Sl ={↑RCB_InvName}=∗
    let e := LocalEvent v (incr_time t i) i (S (size Su)) in
    ⌜e ∉ Su⌝ ∗
    ⌜le_payload e = v⌝ ∗
    ⌜le_orig e = i ⌝ ∗
    ⌜erase e ∉ h⌝ ∗
    ⌜erase e ∈ compute_maximals ge_time (h ∪ {[erase e]})⌝ ∗
    ⌜compute_maximum le_time (Su ∪ {[e]}) = Some e⌝ ∗
    ⌜RCBM_Lst_valid i {| Lst_time := incr_time t i; Lst_hst := Su ∪ {[e]} |}⌝ ∗
    own_global_user γGown γGsnap (h ∪ {[ erase e ]}) ∗
    own_global_snap γGsnap {[ erase e ]} ∗
    lhst_user γLs i (Su ∪ {[ e ]}) ∗
    lhst_lock γLs i (Su ∪ {[ e ]}).
  Proof.
    iIntros (HLvalid) "#HGinv Hglob Huser Hlock".
    set e := LocalEvent v (incr_time t i) i (S (size Su)).
    pose proof (RCBM_LSTV_at HLvalid) as Hlt.
    rewrite -(RCBM_LSTV_time_length HLvalid) in Hlt.
    simpl in Hlt.
    assert (e ∉ Su) as Hes.
    { apply (RCBM_system_global_event_fresh_lhst e i t); done. }
    iDestruct (lhst_user_lock_agree with "Huser Hlock") as %<-.
    iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%HGv)" "Hcl".
    iDestruct (lhst_user_lookup with "HL Huser") as "%Hlookup_i".
    assert (erase e ∉ G) as Heg.
    { eapply RCBM_system_global_event_fresh_gmem; done. }
    assert (erase e ∈ compute_maximals ge_time (G ∪ {[erase e]})) as Herase_max.
    { eapply RCBM_system_global_event_maximals_gmem; eauto. }
    assert (compute_maximum le_time (Su ∪ {[e]}) = Some e) as Hmax.
    { by eapply RCBM_system_global_event_maximum_lhst. }
    assert (RCBM_Lst_valid i (LST (incr_time t i) (Su ∪ {[e]}))) as Hvalid'.
    { eapply (RCBM_lst_update_write e i _ HLvalid); eauto. }
    assert ( RCBM_GstValid
               {| Gst_ghst := {[ erase e ]} ∪ G;
                  Gst_hst := <[i := Su ∪ {[e]}]> Ss |}) as HGv'.
    {  apply (RCBM_system_write_update_gst v i _ _ HLvalid HGv Hlookup_i). }
    iMod (lhst_update _ _ _ _ e with "Huser Hlock HL") as "(Huser & Hlock & HL)".
    iDestruct (own_global_user_sys_agree with "Hglob Hsys") as %->.
    iMod ((own_global_update _ _ _(G ∪ {[ erase e ]})) with "Hglob Hsys") as "[Hglob Hsys]";
      [set_solver |].
    iDestruct (own_global_sys_snap with "Hsys") as "[Hsys #Hsnap]".
    iMod ("Hcl" with "[HL Hsys]") as "_".
    { replace (G ∪ {[ erase e ]}) with ({[ erase e ]} ∪ G); [ | set_solver].
      eauto with iFrame. }
    iDestruct (own_global_snap_weaken _ {[ erase e ]} with "Hsnap") as "#Hsnap'";
      [set_solver |].
    iModIntro. eauto 15 with iFrame.
  Qed.

  Lemma internal_broadcast_spec_holds
        (i : nat) (z : socket_address) (T SeenLoc IQ OQ : loc) (lk : val)
        (γlk : gname) :
    {{{ Global_Inv γGown γGsnap γLs ∗
        local_invariant γGsnap γLs i T SeenLoc IQ OQ lk γlk z }}}
      broadcast #T #SeenLoc #OQ lk #i @[ip_of_address z]
    {{{ br, RET br; internal_broadcast_spec br i z }}}.
  Proof.
    rewrite /broadcast /local_invariant.
    remember (ip_of_address z) as ip.
    iIntros (Φ) "(#Ginv & #Linv) HΦ".
    wp_pures. iApply "HΦ". rewrite /internal_broadcast_spec.
    rewrite -Heqip.
    clear Φ.
    iIntros (v) "%Hiz !> %Φ HΦ".
    wp_pures.
    wp_apply acquire_spec; [iFrame "#" |].
    iIntros (?) "(-> & Hlk & Hli)".
    wp_pures.
    wp_bind (! _)%E.
    iDestruct "Hli" as (vt vseen viq voq t seen liq loq s' ip')
    "(%Hip'& HT & %Hvc & HSeen & %Hvc_seen & %Hlen_eq & HIQ & HOQ & Hlock & %Hvalid)".
    rewrite Hiz in Hip'; simpl in Hip'.
    simplify_eq Hip'; intros <-; rewrite -!Heqip.
    wp_load; simpl.
    assert (i < (length t))%nat as Hlit.
    { erewrite (RCBM_LSTV_time_length Hvalid);
        eauto using RCBM_LSTV_at. }
    destruct (lookup_lt_is_Some_2 _ _ Hlit) as [ti Hti].
    wp_apply (wp_vect_inc); eauto with lia; try lia.
    iIntros (vt' Hvt').
    wp_store. wp_pures.
    wp_load. wp_pures.
    wp_bind (! _)%E.
    wp_load.
    wp_apply wp_vect_nth; [| done |].
    { rewrite incr_time_length; lia. }
    iIntros (sn) "%Hseen".
    destruct Hseen as [sn_val [-> _]].
    wp_pures.
    wp_load.
    wp_apply wp_vect_update; [ | done | ].
    { lia. }
    iIntros (tmp_res) "#Htmp".
    wp_bind (_ <- _)%E.
    (* This is (one posssible) linearization point: we need to logically track the
       newly-broadcasted event. *)
    iApply (aneris_wp_atomic _ _ (↑RCB_InvName)).
    iMod "HΦ". iModIntro. wp_store.
    iDestruct "HΦ" as (h s) "[[Hgu Hu] HΦ]".
    iDestruct (lhst_user_lock_agree with "Hu Hlock") as %<-.
    iMod ((broadcast_ghost_update _ t _ _ _ v) with "[//] Hgu Hu Hlock") as
        "(% & % & % & % & % & % & #HLvalid & Hgu & #Hgsnap & Hu & Hlock)"; [done |].
    remember {| le_payload := v;
                le_time := incr_time t i;
                le_orig := i;
                le_seqid := S (size s) |} as e.
    iAssert (⌜is_lev (v, vt', #i)%V e⌝%I) as "%".
    { rewrite Heqe.
      apply is_vc_vector_clock_to_val in Hvt'; subst.
      simpl.
      iPureIntro.
      rewrite /is_lev. simpl.
      rewrite /is_gev.
      eauto 10 using vector_clock_to_val_is_vc. }
    iMod ("HΦ" with "[$Hu $Hgu]") as "HΦ"; [eauto |].
    iModIntro. wp_pures.
    wp_bind (list_mapi _ _).
    iDestruct "HOQ" as "(HOQ_pt&HilP&#Hlen&Hown_l)".
    wp_load. wp_pures.
    remember (λ: "j" "q",
              if: "j" ≠ #i then queue_add ((v, vt', #i)%V, #i) "q"
              else "q")%V as fv.
    (* Specify a bunch of arguments to wp_list_mapiP that aren't easy to infer *)
    set ev := GlobalEvent v (incr_time t i) i.
    set f : nat -> list global_event -> list global_event :=
      λ j q, if (j =? i) then q else  q ++ [ev].
    set Parg := is_queue.
    set Qarg := Parg.
    set γ := λ i x, single_queue_inv γGsnap i x.
    set ψ := γ.
    iApply ((wp_list_mapiP f _ _ _ Parg Qarg γ ψ) with "[$HilP $Hown_l]").
    { iModIntro.
      subst Parg Qarg γ ψ f.
      iIntros (i' qe qev ϕ).
      iModIntro.
      iIntros "[Hsq_inv %Hisq] Hϕ".
      rewrite /single_queue_inv.
      wp_pures.
      destruct (bool_decide (Z.of_nat i' = Z.of_nat i)) eqn:Heq; wp_pures; last first.
      + apply bool_decide_eq_false in Heq.
        apply Z.eqb_neq in Heq.
        rewrite Heq.
        replace (Val (v, vt', #i)%V) with ($ev : expr); last first; [auto |].
        { simpl.
          apply is_vc_vector_clock_to_val in Hvt'.
          rewrite Hvt'.
          done. }
        wp_apply wp_queue_add; [done |].
        iIntros (rv) "%Hiq'".
        iApply "Hϕ".
        iSplitL ""; [done | ].
        iApply big_sepL_app.
        iFrame.
        iApply big_sepL_singleton.
        assert (erase e = ev) as ->.
        { subst e ev.
          done. }
        iFrame "#".
        iPureIntro.
        subst ev; simpl.
        split; [apply _ |].
        assert (i ≠ i') as ?.
        { intros contra.
          rewrite contra in Heq.
          pose proof (Z.eqb_refl  i') as Heqb.
          rewrite Heqb in Heq.
          done. } 
        rewrite Hiz; eauto.
      + iApply "Hϕ".
        apply bool_decide_eq_true in Heq.
        apply Z.eqb_eq in Heq.
        rewrite Heq.
        iFrame.
        by iPureIntro. }
    iModIntro.
    iIntros (rv) "[%Hrv Hown]".
    wp_store.
    iAssert (OutQueues_inv γGsnap ip OQ (mapi f loq) rv) with "[$HOQ_pt $Hown]" as "HOQ_inv".
    { rewrite mapi_length.
      iFrame "#".
      by iPureIntro. }
    wp_apply (release_spec with "[$Hlk HT HSeen HIQ HOQ_inv Hlock]").
    { iFrame "#".
      rewrite /local_inv_def.
      repeat (iExists _).
      iFrame. iFrame "#".
      rewrite /local_inv_def.
      iPureIntro.
      rewrite Hiz Heqip; simpl.
      rewrite incr_time_length insert_length; done. }
    iIntros (vunit) "->". wp_pures. done.
  Qed.

End proof.

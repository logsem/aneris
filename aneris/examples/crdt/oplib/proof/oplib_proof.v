From stdpp Require Import gmap.
From iris.base_logic Require Import invariants bi.
(* TODO: this should ideally be done in resources.v *)
From aneris.algebra Require Import monotone.
From iris.algebra Require Import auth.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.lib Require Import lock_proof serialization_proof list_proof.
From aneris.examples.rcb.spec Require Import spec.
(* TODO: move wp_loop_forever out of proof_of_network into a more central
   location *)
From aneris.examples.rcb.proof Require Import proof_of_network.
From aneris.examples.rcb Require Import rcb_code.
From aneris.examples.rcb.instantiation Require Import proof events.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.spec Require Import crdt_events crdt_denot crdt_time crdt_base.
From aneris.examples.crdt.oplib.spec Require Import spec events model.
From aneris.examples.crdt.oplib.proof Require Import time params resources.

Section OpLib_Proof.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !OpLib_Params LogOp LogSt}.
  Context `{!Internal_OpLibG LogOp Σ, !OpLib_InvGhostNames}.
  Context `{!RCB_events, !RCB_resources Mdl Σ}.

  (** * Lock invariant *)

  Definition lock_inv_aux (i : nat) (st_loc : loc) : iProp Σ :=
    ∃ (ip : ip_address) (phys_st : val) (log_st : LogSt)
      (h__own h__for : gset (Event LogOp)),
      ⌜ip_of_address <$> CRDT_Addresses !! i = Some ip⌝ ∗
      st_loc ↦[ip] phys_st ∗
      ⌜OpLib_State_Coh log_st phys_st⌝ ∗
      oplib_loc_st_lock_wrap i h__own h__for ∗
      ⌜⟦h__own ∪ h__for⟧ ⇝ log_st⌝.

  Definition lock_inv_ns := nroot.@"lock_inv_ns".

  Definition lock_inv (saddr : socket_address) (γ__lock : gname) (lockv : val)
                      (i : nat) (st_loc : loc) : iProp Σ :=
    is_lock lock_inv_ns (ip_of_address saddr) γ__lock lockv (lock_inv_aux i st_loc).

  (** * get_state spec *)

  Definition internal_get_state_spec (get_state : val) (repId : nat) (saddr : socket_address) : iProp Σ :=
    ⌜CRDT_Addresses !! repId = Some saddr⌝ -∗
    <<< ∀∀ (s1 s2 : gset (Event LogOp)), oplib_loc_st_user_wrap repId s1 s2 >>>
       get_state #() @[ip_of_address saddr] ↑CRDT_InvName
    <<<▷ ∃∃ (s2' : gset (Event LogOp)) (phys_st : val) (log_st : LogSt), RET phys_st;
             ⌜s2 ⊆ s2'⌝ ∗
             oplib_loc_st_user_wrap repId s1 s2' ∗
             ⌜OpLib_State_Coh log_st phys_st⌝ ∗
             ⌜⟦s1 ∪ s2'⟧ ⇝ log_st⌝ >>>.

  Lemma internal_get_state_spec_holds (i : nat) (saddr : socket_address)
      (lockv : val) (st_loc : loc) (γ__lock : gname) :
    {{{ oplib_inv ∗
        lock_inv saddr γ__lock lockv i st_loc }}}
      get_state lockv #st_loc @[ip_of_address saddr]
    {{{ (getst__fun : val), RET getst__fun; internal_get_state_spec getst__fun i saddr }}}.
  Proof.
    iIntros (Φ) "[[#? #?] #Hislock] HΦ".
    rewrite /get_state.
    wp_pures.
    iApply "HΦ". clear Φ.
    iIntros "%Haddr".
    iModIntro.
    iIntros (Φ) "Hpre".
    wp_pures.
    wp_apply (acquire_spec with "Hislock").
    iIntros (v) "[-> [Hlocked Haux]]".
    wp_pures.
    rewrite /lock_inv_aux.
    iDestruct "Haux" as (ip phys_st log_st hown hfor) "(%Hip&Hptr&%Hcoh&Hlock&%Hdenot)".
    rewrite Haddr in Hip. simpl in Hip.
    inversion Hip; subst.
    wp_load.
    (* find an atomic step around which to viewshift *)
    wp_bind (Lam _ _).
    wp_apply (aneris_wp_atomic _ _ (↑CRDT_InvName)).
    iMod "Hpre" as (s1 s2) "[Huser Hclose]".
    (* open invariant *)
    iInv OpLib_InvName as "> Hinvp" "Hclose'".
    iDestruct (oplib_loc_st_user_lt with "Huser") as "%Hlt".
    iDestruct (oplib_inv_lookup_acc' with "Hinvp [//]") as
      (hown' hfor' hsub' hglob) "(Hinv & Hglob & Hacc)".
    iDestruct (loc_st_lock_inv_wrap_agree with "Hinv Hlock") as "%Heq".
    destruct Heq as [-> ->].
    iDestruct (loc_st_user_inv_wrap_agree with "Hinv Huser") as "%Heq".
    destruct Heq as [<- <-].
    iDestruct (loc_st_inv_subseteq with "Hinv") as "%Hsubset".
    iMod (loc_st_user_inv_sub_wrap_update with "Hinv Huser") as "[Hinv Huser]".
    iDestruct ("Hacc" with "[Hinv Hglob]") as "Hinv"; [eauto with iFrame|].
    (* close invariant *)
    iMod ("Hclose'" with "[Hinv]") as "_"; [eauto|].
    iModIntro.
    wp_pures.
    (* complete view shift *)
    iMod ("Hclose" with "[$Huser]") as "HΦ"; [eauto |].
    iModIntro.
    wp_pures.
    assert (ip_of_address <$> CRDT_Addresses !! i = Some (ip_of_address saddr)) as Hip2.
    { rewrite Haddr.
      simpl. done. }
    wp_apply (release_spec with "[$Hislock $Hlocked Hptr Hlock]").
    { rewrite /lock_inv_aux.
      eauto 15 with iFrame. }
    iIntros (v) "_".
    wp_pures.
    iApply "HΦ".
  Qed.

  (** * update spec *)

  Definition internal_update_spec (update : val) (repId : nat) (saddr : socket_address) : iProp Σ :=
    ∀ (op : val) (log_op : LogOp),
     ⌜CRDT_Addresses !! repId = Some saddr⌝ -∗
     ⌜OpLib_Op_Coh log_op op⌝ -∗
     <<< ∀∀ h s1 s2,
         oplib_glob_st_user h ∗
         oplib_loc_st_user_wrap repId s1 s2 >>>
       update op @[ip_of_address saddr] ↑CRDT_InvName
     <<<▷ ∃∃ e (h' s1' s2' : gset (Event LogOp)), RET #();
          ⌜e.(EV_Op) = log_op⌝ ∗
          ⌜e.(EV_Orig) = repId⌝ ∗
          ⌜h' = h ∪ {[ e ]}⌝ ∗
          ⌜s1' = s1 ∪ {[ e ]}⌝ ∗
          ⌜s2 ⊆ s2'⌝ ∗
          ⌜e ∉ h⌝ ∗
          ⌜e ∉ s1⌝ ∗
          ⌜e ∈ Maximals h'⌝ ∗
          ⌜Maximum (s1' ∪ s2') = Some e⌝ ∗
          oplib_glob_st_user h' ∗
          oplib_loc_st_user_wrap repId s1' s2' >>>.

  (* TODO: move somewhere else *)
  Lemma op_coh_sv_val {log_op op} `{!OpLib_Params LogOp LogSt} :
    OpLib_Op_Coh log_op op -> ∃ (sv : base.SerializableVal), op = base.SV_val sv.
  Proof.
    intros Hser%OpLib_Coh_Ser.
    assert (base.RCB_serialization = OpLib_Serialization) as Heq; [done |].
    rewrite <- Heq in Hser.
    exists (@base.SerVal _ op Hser); done.
  Qed.

  Lemma OwnGlobal_ext h E :
    ↑RCB_InvName ⊆ E -> GlobalInv ⊢ OwnGlobal h ={E}=∗ OwnGlobal h ∗ ⌜gstate_ext h⌝.
  Proof.
    iIntros (Hsub) "Hinv Hglob".
    iApply fupd_plain_keep_r.
    iFrame.
    iIntros "Hglob".
    iDestruct (User_Snapshot with "Hglob") as "[Hglob #Hsnap]".
    iMod (Snapshot_ext with "Hinv Hsnap Hsnap") as "%Hext"; [done |].
    iPureIntro.
    done.
  Qed.

  Lemma internal_update_spec_holds (i : nat) (saddr : socket_address)
      (lockv broadcast__fun effect__fun : val) (st_loc : loc) (γ__lock : gname) :
    {{{ oplib_inv ∗
        lock_inv saddr γ__lock lockv i st_loc ∗
        broadcast_spec broadcast__fun i saddr ∗
        effect_spec effect__fun
    }}}
      update lockv broadcast__fun #st_loc effect__fun @[ip_of_address saddr]
    {{{ (update__fun : val), RET update__fun; internal_update_spec update__fun i saddr }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlockinv & #Hbc & #Heff) HΦ".
    rewrite /update.
    wp_pures.
    iApply "HΦ".
    clear Φ.
    rewrite /internal_update_spec.
    iIntros (op log_op) "%Haddr %Hcoh".
    iModIntro.
    iIntros (Φ) "Hvs".
    wp_pures.
    wp_apply (acquire_spec with "Hlockinv").
    iIntros (v) "(Heq & Hlocked & HPlock)".
    pose proof (op_coh_sv_val Hcoh) as [sv ->].
    wp_pures.
    wp_bind (broadcast__fun _).
    iApply "Hbc"; [done |].
    iMod "Hvs" as (h s1 s2) "[(Hglobu & Huser) Hclose]".
    iDestruct "Hinv" as "[#Hrcbinv #Hopinv]".
    iInv OpLib_InvName as "> Hinvp" "Hclose'".
    iDestruct (oplib_loc_st_user_lt with "Huser") as "%Hlt".
    iAssert (⌜i < length CRDT_Addresses⌝%I) as "#Hlt2"; [done |].
    iDestruct (oplib_inv_lookup_acc' with "Hinvp Hlt2") as
      (hown hfor hsub hglob) "(Hlocinv & Hglobi & Hinvcl)".
    iDestruct "HPlock" as (ip phys_st log_st hown' hfor') "(%&Hptr&%Hstcoh&Hlock&%Hdenot)".
    iDestruct (loc_st_user_inv_wrap_agree with "Hlocinv Huser") as "[%Heq1 %Heq2]".
    iDestruct (loc_st_lock_inv_wrap_agree with "Hlocinv Hlock") as "[%Heq3 %Heq4]".
    iDestruct (loc_st_inv_subseteq with "Hlocinv") as "%Hsubseteq".
    subst.
    iDestruct (oplib_loc_st_inv_wrap_pure with "Hlocinv") as "(%Hownorig&%Hfororig&%Hsuborig&%Hcc)".
    iDestruct (oplib_glob_agree with "Hglobu [Hglobi]") as "[Hglobu Hglobi]"; [eauto |].
    iMod (fupd_mask_subseteq (↑RCB_InvName)) as "Hcl".
    {  apply rcb_invname_diff_subseteq. }
    iMod (oplib_loc_inv_subset_glob_internal (↑RCB_InvName) with "Hrcbinv Hlocinv Hlock Hglobi") as "(Hlocinv & Hlock & Hglobi & %Hsubsetglob)"; [done|].
    iModIntro.
    iDestruct (update_own (↑RCB_InvName) with "Hrcbinv Hglobu Hglobi Huser Hlock Hlocinv") as
      (hglob' hloc) "(Hglob'&Hloc&%Hsetcoh&Hacc)"; [set_solver| done |].
    iExists hglob', hloc.
    iFrame.
    iModIntro.
    iIntros (w a) "(%&%&%&%&%&%&%&Hglob&Hloc)".
    iMod (OwnGlobal_ext with "Hrcbinv Hglob") as "[Hglob %Hglobext]"; [done |].
    iMod (OwnLocal_local_ext' with "Hrcbinv Hloc") as "[Hloc %Hlocext]"; [done |].
    iMod ("Hacc" $! a log_op with "[$Hglob $Hloc]") as "Hres".
    { iPureIntro.
      subst.
      match goal with
      | [ H : LE_payload ?x = ?y |- _ ] => rewrite H
      end.
      repeat split; auto. }
    iMod "Hcl" as "_".
    iDestruct "Hres" as (e) "(%&%&%&%&%&%&Hglobi&Hglobu&Hloc&Hlock&Hinv)".
    iDestruct ("Hinvcl" with "[Hinv Hglobi]") as "Hinvcl".
    { iExists _, _, _, _.
      iFrame. }
    match goal with
    | [ H : loc_st_coh _ _ |- _ ] =>
        pose proof H as (Hopcoh & Horigcoh & Hvccoh)
    end.
    assert (EV_Op e = log_op) as Hopeq.
    { eapply OpLib_Op_Coh_Inj; [eauto |].
      match goal with
      | [ H : LE_payload _ = _ |- _ ] =>
          rewrite H; done
      end. }
    iMod ("Hclose'" with "Hinvcl") as "_".
    iDestruct (oplib_loc_st_take_snap with "Hloc") as "[Hloc #Hsnap]".
    iMod (oplib_loc_snap_ext (↑CRDT_InvName) with "[] Hsnap Hsnap") as "%Hext"; [set_solver | iFrame "#" |].
    iMod ("Hclose" $! e _ _ hfor' with "[Hglobu Hloc]") as "HΦres".
    { iFrame.
      iPureIntro.
      subst.
      repeat split; auto. }
    iModIntro.
    wp_pures.
    match goal with
    | [ H : fmap _ _ = _ |- _ ] =>
        pose proof H as Hfmap
    end.
    rewrite Haddr in Hfmap.
    inversion Hfmap.
    subst.
    wp_load.
    iDestruct ("Heff" $! saddr w phys_st (hown' ∪ hfor') e log_st) as "Heff'".
    assert (e ∉ hown' ∪ hfor') as Hnotin.
    { intros [Hl|Hr%Hfororig]%elem_of_union; [set_solver|].
      apply Hr; done. }
    lazymatch goal with
    | [ H : Maximum _ = _ |- _ ] =>
        pose proof H as Hmaxi
    end.
    assert (hown' ∪ {[e]} ∪ hfor' = (hown' ∪ hfor') ∪ {[e]}) as Hset.
    { set_solver. }
    wp_apply "Heff'".
    { assert (hown' ∪ hfor' ∪ {[e]} = hown' ∪ {[e]} ∪ hfor') as ->; [set_solver|].
      iPureIntro; (repeat split); eauto.
      - rewrite /OpLib_Event_Coh.
        match goal with
        | [ H : is_le _ _ |- _ ] =>
            pose proof H as (p & vc & o & -> & Hle1 & Hle2 & Hle3)
        end.
        exists p, vc, o.
        assert ((SV_val sv) = p) as <-.
        { subst.
          match goal with
          | [ H : LE_payload _ = _ |- _ ] =>
              rewrite <- H
          end.
          rewrite erasure_payload.
          done. }
        rewrite /time /Event_Timed.
        assert (GE_vc (erasure a) = (EV_Time e)) as <-.
        { match goal with
          | [ H : _ = LE_vc _ |- _ ] =>
              rewrite H
          end.
          rewrite erasure_vc.
          done. }
        assert (GE_origin (erasure a) = EV_Orig e) as <-.
        { match goal with
          | [ H : EV_Orig _ = _ |- _ ] =>
              rewrite H
          end.
          rewrite erasure_origin.
          done. }
        eauto.
      - set_solver.
      - intros e' He'in contra.
        apply Maximum_correct in Hmaxi; [ | apply Hext].
        destruct (decide (e = e')) as [->|Hr].
        + apply TM_lt_irreflexive in contra.
          done.
        + destruct Hmaxi as [_ Hmaxi].
          assert (e' ≠ e) as Hr'; [done |].
          pose proof (Hmaxi e' He'in Hr') as Hfoo.
          assert (e <_t e) as ?.
          { eapply TM_lt_trans; done. }
          eapply TM_lt_irreflexive; eauto.
    }
    iIntros (st') "Hpre".
    iDestruct "Hpre" as (log_st') "(%Hst_coh'&%Hmod_eff)".
    wp_store.
    wp_apply (release_spec with "[-HΦres]").
    { iFrame "#". iFrame.
      rewrite /lock_inv_aux.
      iExists _,_, _, _, _.
      iFrame.
      iPureIntro.
      repeat split; eauto.
      rewrite Hset.
      eapply op_crdt_effect_coh; eauto.
      - apply is_maximum_maximal.
        apply Maximum_correct in Hmaxi; [ | apply Hext].
        rewrite Hset in Hmaxi.
        done.
      - eapply lstate_events_ext; last first.
        + rewrite /lstate_ext.
          eapply Hlocext.
        + apply loc_st_set_coh_union; done.
      - assert (hown' ∪ hfor' ∪ {[e]} = (hown' ∪ {[e]} ∪ hfor')) as ->; [set_solver|done].
    }
    iIntros (?) "->".
    iFrame.
  Qed.

  (** * apply thread *)
  Lemma glob_st_snapshot_coh E h g :
    ↑RCB_InvName ⊆ E ->
    GlobalInv ⊢
    oplib_glob_st_inv h -∗
    OwnGlobalSnapshot {[ g ]} ={E}=∗
    ∃ e, oplib_glob_st_inv h ∗ ⌜glob_st_coh e g ∧ e ∈ h⌝.
  Proof.
    iIntros (Hsub) "#Hglobinv Hglob #Hsnap".
    iDestruct "Hglob" as (s) "(Hownglob & Hown & %Hcoh)".
    iMod (OwnGlobalSnapshot_included with "Hglobinv Hownglob Hsnap") as
      "[Hownglob %Hsubseteq]"; [done |].
    apply singleton_subseteq_l in Hsubseteq.
    apply Hcoh in Hsubseteq as [p [Hin Hcoh']].
    iModIntro.
    rewrite /oplib_glob_st_inv.
    eauto with iFrame.
  Qed.

  Lemma glob_st_coh_op_coh e g :
    glob_st_coh e g -> OpLib_Op_Coh (EV_Op e) (GE_payload g).
  Proof.
    by intros (? & _ & _).
  Qed.

  (* TODO: move to resources *)
  Lemma oplib_glob_st_inv_total h : oplib_glob_st_inv h ⊢ ⌜events_total_order h⌝.
  Proof.
    iIntros "Hglob".
    by iDestruct "Hglob" as (a) "(_&_&_&%)".
  Qed.

  Lemma apply_thread_spec i saddr lockp deliver_fun stp effect_fun γlock :
    {{{
      ⌜RCB_addresses !! i = Some saddr⌝ ∗
      oplib_inv ∗
      lock_inv saddr γlock lockp i stp ∗
      deliver_spec deliver_fun i saddr ∗
      effect_spec effect_fun
    }}}
      apply_thread lockp deliver_fun #stp effect_fun @[ip_of_address saddr]
    {{{
      RET #(); False (* infinite loop: doesn't terminate *)
    }}}.
  Proof.
    iIntros (Φ) "(%Haddr & [#Hrcbinv #Hinv] & #Hlockinv & #Hdeliver & #Heffect) HΦ".
    rewrite /apply_thread.
    wp_pures.
    wp_apply (wp_loop_forever _ True with "[Hlockinv]");
      [ | done].
    clear Φ.
    iSplitL ""; [ | done].
    iIntros "!>" (Φ) "_ HΦ".
    wp_pures.
    wp_apply (acquire_spec with "[Hlockinv]").
    { rewrite /lock_inv. iFrame "#". }
    iIntros (v) "(-> & Hlocked & Hlockp)".
    wp_pures.
    wp_apply "Hdeliver"; [done |].
    iInv OpLib_InvName as "> Hinvp" "Hclose'".
    iDestruct "Hlockp" as (ip phys log hown hfor) "(%&Hstptr&%Hopcoh&Hlockwrap&%Hdenot)".
    iDestruct (oplib_loc_st_lock_lt with "Hlockwrap") as "%Hlt".
    iAssert (⌜i < length CRDT_Addresses⌝%I) as "#Hlt2"; [done |].
    iDestruct (oplib_inv_lookup_acc' with "Hinvp Hlt2") as
      (hown' hfor' hsub' hglob) "(Hlocinv & Hglob & Hinvcl)".
    iDestruct (loc_st_lock_inv_wrap_agree with "Hlocinv Hlockwrap") as "[%Heqown %Heqfor]".
    (* iDestruct (loc_st_inv_subseteq with "Hlocinv") as "%Hsubseteq". *)
    subst.
    iDestruct (update_foreign with "Hlockwrap Hlocinv") as (s) "[Hownloc [%Hsetcoh Hacc]]".
    iApply fupd_mask_intro.
    { apply rcb_invname_subseteq_mask. done. }
    iIntros "Hmaskcl".
    iExists s. iFrame.
    iModIntro.
    iIntros (s' vo) "(Hownloc & [[-> ->] | Hr])".
    - (* received nothing *)
      iMod ("Hmaskcl").
      iDestruct "Hacc" as "[_ Hacc]".
      iDestruct ("Hacc" with "Hownloc") as "[Hlock'' Hinv'']".
      iDestruct ("Hinvcl" with "[Hinv'' Hglob]") as "Hinvprop".
      { iExists _, _, _, _.
        iFrame. }
      iMod ("Hclose'" with "[Hinvprop]") as "_"; [done |].
      iModIntro.
      wp_pures.
      wp_apply (release_spec with "[$Hlockinv $Hlocked Hstptr Hlock'']").
      { rewrite /lock_inv_aux.
        eauto 15 with iFrame. }
      iIntros (v) "->".
      by iApply "HΦ".
    - iDestruct "Hacc" as "[Hacc _]".
      iDestruct "Hr" as (a) "(%&%&%&%&#Hglobsnap&Hv)".
      iDestruct "Hv" as (v) "[-> %Hle]".
      (* produce the operation corresponding to the message *)
      (* use the fact that the snapshot is included in OwnGlobal *)
      iMod (glob_st_snapshot_coh with "Hrcbinv Hglob Hglobsnap") as
        (e) "[Hglob [%Hglobcoh %Hin]]"; [done |].
      apply glob_st_coh_op_coh in Hglobcoh as Hopcoh'.
      rewrite erasure_payload in Hopcoh'.
      subst.
      iMod (OwnLocal_local_ext' with "Hrcbinv Hownloc") as "[Hownloc %Hext]"; [done |].
      iMod ("Hacc" $! a (EV_Op e) with "[$Hownloc]") as
        (e') "(%Hloccoh&%Henotin&%Hemaxi&Hlock&Hinv')"; [eauto |].
      assert (e = e') as ->.
      { apply loc_st_coh_glob_st_coh in Hloccoh.
        eapply glob_st_coh_inj; done. }
      iDestruct (oplib_glob_st_inv_total with "Hglob") as "%Htot".
      iMod (oplib_loc_inv_subset_glob_internal with "Hrcbinv Hinv' Hlock Hglob") as "(Hinv' & Hlock & Hglob & %Hsubseteq')"; [done|].
      iMod ("Hmaskcl") as "_".
      iDestruct ("Hinvcl" with "[Hglob Hinv']") as "Hinvprop".
      { iExists _, _, _, _.
        iFrame. }
      iMod ("Hclose'" with "[Hinvprop]") as "_"; [by iFrame|].
      iModIntro.
      wp_pures.
      assert (ip_of_address saddr = ip) as <-.
      { match goal with
        | [ H : fmap _ _ = _ |- _ ] =>
            pose proof H as Haddr'
        end.
        simpl in *.
        rewrite Haddr in Haddr'.
        simpl in Haddr'.
        inversion Haddr'.
        done. }
      wp_load.
      iDestruct (oplib_loc_st_lock_orig with "Hlock") as "%Horig".
      destruct Horig as [Hownorig _].
      wp_apply "Heffect".
      { iAssert (⌜OpLib_Event_Coh e' v⌝%I) as "Hevcoh".
        { iPureIntro.
          rewrite /OpLib_Event_Coh.
          rewrite /is_le /is_ge in Hle.
          destruct Hle as (p & vc & o & -> & -> & Hvc & ->).
          eexists _, _, _.
          repeat split; eauto.
          - simpl.
            rewrite erasure_payload.
            done.
          - rewrite /time /Event_Timed.
            assert (GE_vc (erasure a) = (EV_Time e')) as <-; [ | done].
            rewrite /glob_st_coh in Hglobcoh.
            destruct Hglobcoh as (?&?&->).
            done.
          - simpl.
            destruct Hglobcoh as (?&->&?).
            done. }
        iFrame "Hevcoh".
        do 2 (iSplitL ""; [by iPureIntro|]).
        iPureIntro.
        split; [|split]; [| | split].
        - intros [Hl|Hr]%elem_of_union; [ | done].
          apply Hownorig in Hl.
          match goal with
          | [H :  LE_origin _ ≠ _ |- _] => apply H
          end.
          rewrite <- Hl.
          destruct Hloccoh as (?&?&?).
          done.
        - apply Maximals_correct in Hemaxi.
          done.
        - eapply lstate_events_ext.
          + eapply loc_st_set_coh_union; eauto.
          + rewrite /lstate_ext. apply Hext.
        - assert (hown ∪ hfor ∪ {[e']} = hown ∪ (hfor ∪ {[e']})) as ->; [set_solver|].
          eapply events_total_order_sub; eauto.
      }
      iIntros (st') "Hexists".
      wp_store.
      iDestruct "Hexists" as (log_st') "[%Hst_coh %Heff]".
      wp_apply (release_spec with "[$Hlocked Hlock $Hlockinv Hstptr]").
      { rewrite /lock_inv_aux.
        iExists _, _, _, _, _.
        iFrame.
        iPureIntro; repeat split; eauto.
        assert (hown ∪ (hfor ∪ {[e']}) = ((hown ∪ hfor) ∪ {[e']})) as ->.
        { set_solver. }
        eapply op_crdt_effect_coh; eauto.
        - intros [Hl|Hr]%elem_of_union.
          + apply Hownorig in Hl.
            match goal with
            | [H :  LE_origin _ ≠ _ |- _] => apply H
            end.
            rewrite <- Hl.
            destruct Hloccoh as (?&?&?).
            done.
          + apply Henotin; done.
        - apply Maximals_correct in Hemaxi.
          done.
        - eapply lstate_events_ext; last first.
          + rewrite /lstate_ext.
            eapply Hext.
          + eapply loc_st_set_coh_union; done.
        - eapply events_total_order_sub.
          + assert ( hown ∪ hfor ∪ {[e']} =  hown ∪ (hfor ∪ {[e']})) as ->; [set_solver|done].
          + done.
      }
      iIntros (?) "->".
      iApply "HΦ". done.
  Qed.

  (** * Init spec *)
  Definition ser_fun : val := OpLib_Serialization.(s_serializer).(s_ser).
  Definition deser_fun : val := OpLib_Serialization.(s_serializer).(s_deser).

  (* BEGIN TODO: cleanup by moving the resources to resources.v *)
  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Definition user_tok i γown γsub γcc : iProp Σ :=
    ⌜γ_own !! i = Some γown⌝ ∗
    ⌜γ_sub !! i = Some γsub⌝ ∗
    ⌜γ_cc !! i = Some γcc⌝ ∗
    own γown ((1/3)%Qp, to_agree ∅) ∗
    own γsub ((2/3)%Qp, to_agree ∅) ∗
    own γcc (◯ (princ_ev ∅)).

  Definition lock_tok i γown γfor : iProp Σ :=
    ⌜γ_own !! i = Some γown⌝ ∗
    ⌜γ_for !! i = Some γfor⌝ ∗
    own γown ((1/3)%Qp, to_agree ∅) ∗
    own γfor ((1/2)%Qp, to_agree ∅).

  (* This can be removed once we move the code to resources.v *)
  Ltac rewrite_lookup := repeat (
    match goal with
    | [ H1 : _ !! ?i = Some ?v1, H2 : _ !! ?i = Some ?v2 |- _ ] =>
          rewrite H1 in H2; inversion H2
    end); subst.

  Lemma loc_st_set_coh_empty_l s :
    loc_st_set_coh ∅ s -> s = ∅.
  Proof.
    intros Hcoh.
    destruct Hcoh as [Hlr Hrl].
    destruct (decide (s = ∅)) as [-> | Hnon]; [done |].
    apply set_choose_L in Hnon as [x Hin%Hrl].
    exfalso.
    destruct Hin as [p [Hin _]].
    apply not_elem_of_empty in Hin.
    done.
  Qed.

  Lemma oplib_inv_start (E : coPset) i γown γfor γsub γcc :
    ↑OpLib_InvName ⊆ E ->
    oplib_inv -∗
    OwnLocal i ∅ -∗
    user_tok i γown γsub γcc -∗
    lock_tok i γown γfor ={E}=∗
      oplib_loc_st_user_wrap i ∅ ∅ ∗
      oplib_loc_st_lock_wrap i ∅ ∅.
  Proof.
    iIntros (Hin) "[_ #Hinv] Hownloc Huser Hlock".
    iInv OpLib_InvName as "> Hinvp" "Hclose'".
    iAssert (⌜γ_cc !! i = Some γcc⌝%I) with "[Huser]" as "%Hlt".
    { iDestruct "Huser" as "(%&%&%&_)".
      done. }
    apply γ_cc_lookup_lt in Hlt.
    iDestruct (oplib_inv_lookup_acc' with "Hinvp [//]") as
          (hown hfor hsub hglob) "(Hinvwrap & Hglob & Hacc)".
    iDestruct "Hinvwrap" as (γown' γfor' γsub' γcc' γinv' s)
                              "(%&%&%&%&%&%Hcoh&%&%&%&%&Hopt&Hown&Hfor&Hsub&Hcc)".
    (* prove that s is the empty set *)
    iAssert (⌜s = ∅⌝%I) with "[Hlock Hown Hfor]" as "%Hseq".
    { iDestruct "Hlock" as "(%&%&Hown'&Hfor')".
      rewrite_lookup.
      iDestruct (pair_agree with "Hown Hown'") as %->.
      iDestruct (pair_agree with "Hfor Hfor'") as %->.
      iPureIntro.
      assert ((∅ ∪ ∅ : gset (Event LogOp)) = ∅) as Heq; [set_solver|].
      rewrite Heq in Hcoh.
      apply loc_st_set_coh_empty_l in Hcoh.
      done. }
    subst.
    iDestruct "Hopt" as "[Huninit|[_ Hr]]"; last first.
    { iExFalso.
      iApply (OwnLocal_Exclusive with "Hownloc Hr"). }
    iMod (inv_own_update with "Huninit") as "#Hinit".
    iDestruct ("Hacc" with "[Hownloc Hown Hfor Hsub Hcc Hglob]") as "Hprop".
    { iExists _, _, _, _.
      iFrame.
      rewrite /oplib_loc_st_inv_wrap.
      iExists _, _, _, _, _, _.
      iFrame.
      repeat (iSplitL ""; [done|]).
      iRight.
      iFrame "#"; iFrame. }
    iMod ("Hclose'" with "[Hprop]") as "_"; [iModIntro; done|].
    iModIntro.
    iSplitL "Huser".
    - iExists _, _, _, _.
      rewrite /oplib_loc_st_user.
      iDestruct "Huser" as "(%&%&%&?&?&?)".
      rewrite /oplib_loc_snap.
      repeat (iSplitL ""; [iPureIntro; done|]).
      iFrame. iFrame "#".
      assert ((∅ ∪ ∅ : gset (Event LogOp)) = ∅) as ->; [set_solver|].
      eauto with iFrame.
    - iExists _, _, _.
      rewrite /oplib_loc_st_lock.
      iDestruct "Hlock" as "(%&%&?&?)".
      iFrame. iFrame "#".
      iPureIntro; done.
  Qed.
  (* END TODO *)

  Definition internal_init_spec : iProp Σ :=
    ∀ (i : nat) addr addrs_val crdt_val,
    {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
         ⌜CRDT_Addresses !! i = Some addr⌝ ∗
         ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ RCB_socket_proto i) ∗
         addr ⤳ (∅, ∅) ∗
         unbound {[addr]} ∗
         (∃ γown γfor γsub γcc,
             init_token i ∗
             user_tok i γown γsub γcc ∗
             lock_tok i γown γfor) ∗
         crdt_fun_spec crdt_val
    }}}
      oplib_init ser_fun
                 deser_fun
                 addrs_val
                 #i
                 crdt_val @[ip_of_address addr]
    {{{ gs_val upd_val, RET (gs_val, upd_val);
        oplib_loc_st_user_wrap i ∅ ∅ ∗
        internal_get_state_spec gs_val i addr ∗
        internal_update_spec upd_val i addr
    }}}.

  Lemma internal_init_spec_holds :
    oplib_inv ⊢ init.init_spec (rcb_code.rcb_init ser_fun deser_fun) -∗ internal_init_spec.
  Proof.
    iIntros "#Hinv #Hinit" (i addr addrs_val crdt_val).
    iModIntro.
    iIntros (Φ) "(%Hil&%Hlookup&#Hproto&Hpts&Hfree&Htok&#Hfun) HΦ".
    rewrite /oplib_init.
    wp_pures.
    iDestruct "Htok" as (γown γfor γsub γcc) "(Hrcbtok & Husertok & Hlocktok)".
    wp_apply ("Hinit" with "[//] [//] [$Hrcbtok $Hpts $Hproto $Hfree]").
    iIntros (del br) "(Hownloc & #Hdelspec & #Hbrspec)".
    wp_apply fupd_aneris_wp.
    iMod (oplib_inv_start with "Hinv Hownloc Husertok Hlocktok") as "[Huserw Hlockw]"; [done |].
    iModIntro.
    wp_pures.
    wp_apply "Hfun"; [done |].
    iIntros (pair) "Hpair".
    wp_pures.
    rewrite /crdt_pair_spec.
    iDestruct "Hpair" as (initv effv) "(->&#Hinitspec&#Heffspec)".
    wp_pures.
    wp_apply "Hinitspec"; [done |].
    iIntros (v) "%Hcoh".
    wp_alloc ℓst as "Hst".
    wp_pures.
    wp_apply (newlock_spec lock_inv_ns _ (lock_inv_aux i ℓst) with "[Hlockw Hst]").
    { rewrite /lock_inv_aux.
      iExists _, _, _, ∅, ∅.
      iFrame.
      iPureIntro.
      assert (∅ ∪ ∅ = ∅) as ->; [set_solver|].
      rewrite Hlookup.
      repeat split; eauto.
      auto using op_crdtM_init_st_coh. }
    iIntros (lk γ) "#Hislock".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HΦ Huserw"; iModIntro.
    - wp_pures.
      wp_apply internal_update_spec_holds; [iFrame "#"|].
      iIntros (updf) "#Hupdspec".
      wp_apply internal_get_state_spec_holds; [iFrame "#"|].
      iIntros (getsf) "#Hgetspec".
      wp_pures.
      iApply "HΦ".
      iFrame; iFrame "#".
    - wp_apply apply_thread_spec; [|done].
      iFrame "#".
      simpl in *; done.
  Qed.

End OpLib_Proof.

Section ResourcesAlloc.

  Context `{LogOp, LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !Internal_OpLibG LogOp Σ, !CRDT_Params}.

  Definition owni (γ_own : list gname) i : iProp Σ :=
    ∃ γown,
      ⌜γ_own !! i = Some γown⌝ ∗
      own γown ((1/3)%Qp, to_agree ∅).

    (* TODO: the allocation lemmas should be moved to resources.v and ideally the proofs'
     commonalities can be factoured out. *)
  Lemma alloc_own : True ⊢ |==> ∃ γ_own,
                        ⌜length γ_own = length CRDT_Addresses⌝ ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, owni γ_own i) ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, owni γ_own i) ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, owni γ_own i).
  Proof.
    iIntros (_).
    iInduction CRDT_Addresses as [|addrs] "IH"; simpl.
    - iModIntro.
      iExists nil.
      iSplitL; [done |].
      done.
    - iMod "IH".
      iDestruct "IH" as (γ_own) "[%Hlen (Hown1 & Hown2 & Hown3)]".
      iMod (own_alloc (((1/3)%Qp, to_agree ∅) ⋅ ((1/3)%Qp, to_agree ∅) ⋅ ((1/3)%Qp, to_agree ∅))) as (γ') "Hnew".
      { rewrite -pair_op. simpl.
        do 2 rewrite frac_op.
        apply pair_valid; split.
        + apply frac_valid.
          compute; done.
        + do 2 rewrite agree_idemp.
          done. }
      iDestruct (own_op with "Hnew") as "[Hnew H1]".
      iDestruct (own_op with "Hnew") as "[H2 H3]".
      iModIntro.
      iExists (γ' :: γ_own).
      iSplitL "".
      + iPureIntro.
        simpl. rewrite Hlen. done.
      + iSplitL "H1 Hown1".
        { iFrame.
          iExists γ'; eauto with iFrame. }
        iSplitL "H2 Hown2".
        { iFrame.
          iExists γ'; eauto with iFrame. }
        iFrame.
        iExists γ'; eauto with iFrame.
  Qed.

  Lemma alloc_for : True ⊢ |==> ∃ γ_for,
                        ⌜length γ_for = length CRDT_Addresses⌝ ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γfor, ⌜γ_for !! i = Some γfor⌝ ∗  own γfor ((1/2)%Qp, to_agree ∅)) ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γfor, ⌜γ_for !! i = Some γfor⌝ ∗  own γfor ((1/2)%Qp, to_agree ∅)).
  Proof.
    iIntros (_).
    iInduction CRDT_Addresses as [|addrs] "IH"; simpl.
    - iModIntro.
      iExists nil.
      done.
    - iMod "IH".
      iDestruct "IH" as (γ_for) "[%Hlen [Hown1 Hown2]]".
      iMod (own_alloc (((1/2)%Qp, to_agree ∅) ⋅ ((1/2)%Qp, to_agree ∅))) as (γ') "Hnew".
      { rewrite -pair_op. simpl.
        rewrite frac_op.
        apply pair_valid; split.
        + apply frac_valid.
          compute; done.
        + rewrite agree_idemp.
          done. }
      iDestruct (own_op with "Hnew") as "[H1 H2]".
      iModIntro.
      iExists (γ' :: γ_for).
      iSplitL "".
      + iPureIntro.
        simpl. rewrite Hlen. done.
      + iSplitL "H1 Hown1".
        { iFrame. eauto with iFrame. }
        iFrame.
        eauto with iFrame.
  Qed.

  Lemma alloc_sub : True ⊢ |==> ∃ γ_sub,
                        ⌜length γ_sub = length CRDT_Addresses⌝ ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γsub, ⌜γ_sub !! i = Some γsub⌝ ∗  own γsub ((2/3)%Qp, to_agree ∅)) ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γsub, ⌜γ_sub !! i = Some γsub⌝ ∗  own γsub ((1/3)%Qp, to_agree ∅)).
  Proof.
    iIntros (_).
    iInduction CRDT_Addresses as [|addrs] "IH"; simpl.
    - iModIntro.
      iExists nil.
      done.
    - iMod "IH".
      iDestruct "IH" as (γ_sub) "[%Hlen [Hown1 Hown2]]".
      iMod (own_alloc (((2/3)%Qp, to_agree ∅) ⋅ ((1/3)%Qp, to_agree ∅))) as (γ') "Hnew".
      { rewrite -pair_op. simpl.
        rewrite frac_op.
        apply pair_valid; split.
        + apply frac_valid.
          compute; done.
        + rewrite agree_idemp.
          done. }
      iDestruct (own_op with "Hnew") as "[H1 H2]".
      iModIntro.
      iExists (γ' :: γ_sub).
      iSplitL "".
      + iPureIntro.
        simpl. rewrite Hlen. done.
      + iSplitL "H1 Hown1"; iFrame; eauto with iFrame.
  Qed.

  (* BEGIN TODO: cleanup by moving the resources to resources.v *)
  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Lemma alloc_cc : True ⊢ |==> ∃ γ_cc,
                        ⌜length γ_cc = length CRDT_Addresses⌝ ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γcc, ⌜γ_cc !! i = Some γcc⌝ ∗ own γcc (● (princ_ev ∅))) ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses, ∃ γcc, ⌜γ_cc !! i = Some γcc⌝ ∗ own γcc (◯ (princ_ev ∅))).
  Proof.
    iIntros (_).
    iInduction CRDT_Addresses as [|addrs] "IH"; simpl.
    - iModIntro.
      iExists nil.
      done.
    - iMod "IH".
      iDestruct "IH" as (γ_cc) "[%Hlen [Hown1 Hown2]]".
      iMod (own_alloc ((● (princ_ev ∅)) ⋅ (◯ (princ_ev ∅)))) as (γ') "Hnew".
      { apply auth_both_valid; done. }
      iDestruct (own_op with "Hnew") as "[H1 H2]".
      iModIntro.
      iExists (γ' :: γ_cc).
      iSplitL "".
      + iPureIntro.
        simpl. rewrite Hlen. done.
      + iSplitL "H1 Hown1"; iFrame; eauto with iFrame.
  Qed.

  Lemma alloc_inv : True ⊢ |==> ∃ (γ_inv : list gname),
                        ⌜length γ_inv = length CRDT_Addresses⌝ ∗
                        ([∗ list] i ↦ _ ∈ CRDT_Addresses,
                          ∃ γinv,
                            ⌜γ_inv !! i = Some γinv⌝ ∗
                            own γinv (inv_uninit : cmra_car oneShotR)).
  Proof.
    iIntros (_).
    iInduction CRDT_Addresses as [|addrs] "IH"; simpl.
    - iModIntro.
      iExists nil.
      done.
    - iMod "IH".
      iDestruct "IH" as (γ_inv) "[%Hlen Hown]".
      iMod (own_alloc (inv_uninit : cmra_car oneShotR)) as (γ') "Hnew"; [done |].
      iModIntro.
      iExists (γ' :: γ_inv).
      iSplitL "".
      + iPureIntro.
        simpl. rewrite Hlen. done.
      + iFrame.
        eauto with iFrame.
  Qed.

  Lemma alloc_glob : True ⊢ |==> ∃ γglob, own γglob ((2/3)%Qp, to_agree ∅) ∗
                                           own γglob ((1/3)%Qp, to_agree ∅).
  Proof.
    iMod (own_alloc (((2/3)%Qp, to_agree ∅) ⋅ ((1/3)%Qp, to_agree ∅))) as (γ') "[H1 H2]".
    { rewrite pair_valid. split.
      + simpl. apply frac_valid.
        compute. done.
      + simpl. rewrite agree_idemp. done. }
    iIntros (_).
    eauto with iFrame.
  Qed.

End ResourcesAlloc.

Section OpLibSetup.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
        !CRDT_Params, !OpLib_Params LogOp LogSt, !Internal_OpLibG LogOp Σ, !RCBG Σ}.

  Definition oplib_init_token `{!RCB_params,
                                !RCB_events,
                                !RCB_resources Mdl Σ,
                                !OpLib_InvGhostNames} i : iProp Σ :=
    ∃ γown γfor γsub γcc,
             init_token i ∗
             user_tok i γown γsub γcc ∗
             lock_tok i γown γfor.

  (* TODO: cleanup *)
  Ltac rewrite_lookup := repeat (
    match goal with
    | [ H1 : _ !! ?i = Some ?v1, H2 : _ !! ?i = Some ?v2 |- _ ] =>
          rewrite H1 in H2; inversion H2
    end); subst.

  Lemma oplib_setup E :
    True ⊢ |={E}=> ∃ (RCB_res : RCB_resources Mdl Σ)
                 (GNames : OpLib_InvGhostNames),
      oplib_inv ∗
      oplib_glob_st_user ∅ ∗
      ([∗ list] i ↦ _ ∈ CRDT_Addresses, oplib_init_token i) ∗
      internal_init_spec.
  Proof.
    iIntros (_).
    iMod (@RCB_init_setup _ _ _ _ _ rcb_init E with "[//]") as (rcb_res) "(#Hrcbinv & Hrcbtok & Hownglob & #Hrcbinit)".
    iExists rcb_res.
    iMod (alloc_own with "[//]") as (γ_own) "[%Hownlen (Hown1 & Hown2 & Hown3)]".
    iMod (alloc_for with "[//]") as (γ_for) "[%Hforlen [Hfor1 Hfor2]]".
    iMod (alloc_sub with "[//]") as (γ_sub) "[%Hsublen [Hsub1 Hsub2]]".
    iMod (alloc_cc with "[//]") as (γ_cc) "[%Hcclen [Hcc1 Hcc2]]".
    iMod (alloc_inv with "[//]") as (γ_inv) "[%Hinvstlen Hinvst]".
    iMod (alloc_glob with "[//]") as (γ_glob) "[Hglobu Hglobinv]".
    set Hnames := (Build_OpLib_InvGhostNames _ γ_glob γ_own γ_for γ_sub γ_cc γ_inv Hownlen Hforlen Hsublen Hcclen Hinvstlen).
    iMod (inv_alloc OpLib_InvName _ (@oplib_loc_st_inv_prop _ _ _ _ _ _ _ _ _ _ _ _ Hnames) with "[Hown1 Hfor1 Hsub2 Hinvst Hglobinv Hownglob Hcc1]") as "#Hinv".
    { iModIntro.
      iSplitL "Hglobinv Hownglob".
      { iExists ∅.
        rewrite /oplib_glob_st_inv.
        eauto with iFrame. }
      iDestruct (big_sepL_sep_2 with "Hown1 Hfor1") as "Hinv".
      iDestruct (big_sepL_sep_2 with "Hinv Hsub2") as "Hinv".
      iDestruct (big_sepL_sep_2 with "Hinv Hinvst") as "Hinv".
      iDestruct (big_sepL_sep_2 with "Hinv Hcc1") as "Hinv".
      iApply (big_sepL_impl with "Hinv").
      iModIntro.
      iIntros (k a) "%Hlookup [[[[Hown Hfor] Hsub] Hinv] Hcc]".
      rewrite /owni.
      iDestruct "Hown" as (γown) "[% Hown]".
      iDestruct "Hfor" as (γfor) "[% Hfor]".
      iDestruct "Hsub" as (γsub) "[% Hsub]".
      iDestruct "Hinv" as (γinv) "[% Hinv]".
      iDestruct "Hcc" as (γcc) "[% Hcc]".
      iExists ∅, ∅, ∅.
      rewrite /oplib_loc_st_inv_wrap.
      iExists γown, γfor, γsub, γcc, γinv, ∅.
      rewrite /oplib_loc_st_inv.
      simpl.
      assert (∅ ∪ ∅ = (∅ : gset (Event LogOp))) as ->; [set_solver|].
      eauto with iFrame. }
    iModIntro.
    iExists Hnames.
    iAssert (oplib_inv) as "Hoplibinv".
    { rewrite /oplib_inv; iFrame "#". }
    iDestruct (internal_init_spec_holds with "Hoplibinv Hrcbinit") as "Hinit".
    iFrame "#"; iFrame "Hglobu".
    iDestruct (big_sepL_sep_2 with "Hrcbtok Hown2") as "Hbig".
    iDestruct (big_sepL_sep_2 with "Hbig Hown3") as "Hbig".
    iDestruct (big_sepL_sep_2 with "Hbig Hfor2") as "Hbig".
    iDestruct (big_sepL_sep_2 with "Hbig Hsub1") as "Hbig".
    iDestruct (big_sepL_sep_2 with "Hbig Hcc2") as "Hbig".
    simpl.
    iApply (big_sepL_impl with "Hbig").
    iModIntro.
    iIntros (k a) "%Hlookup".
    iIntros "[[[[[Hrcbtok Hown1] Hown2] Hfor] Hsub] Hcc]".
    rewrite /oplib_init_token.
    iDestruct "Hown1" as (γown) "[% Hown]".
    iDestruct "Hown2" as (γown') "[% Hown']".
    rewrite_lookup.
    iDestruct "Hfor" as (γfor) "[% Hfor]".
    iDestruct "Hsub" as (γsub) "[% Hsub]".
    iDestruct "Hcc" as (γcc) "[% Hcc]".
    iExists γown', γfor, γsub, γcc.
    iFrame. simpl.
    done.
  Qed.

End OpLibSetup.

Section Instantiation.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !OpLib_Params LogOp LogSt, !Internal_OpLibG LogOp Σ,
            !RCBG Σ}.

  Global Instance init_fun_instance : OpLib_Init_Function := { init := oplib_init ser_fun deser_fun }.
  Global Instance oplib_res_instance `{!RCB_resources Mdl Σ, !OpLib_InvGhostNames} : OpLib_Res LogOp := {
      OpLib_InitToken := oplib_init_token;
      OpLib_SocketProto := RCB_socket_proto;
  }.

  Program Global Instance oplib_setup_instance : OpLibSetup.
  Next Obligation.
    iIntros (E) "_".
    iMod (oplib_setup with "[//]") as (res names) "(#Hinv & Hglob & Htoks & #Hinit)".
    iModIntro.
    iExists oplib_res_instance.
    simpl.
    iFrame "Hinv Hglob Htoks Hinit".
  Qed.

End Instantiation.

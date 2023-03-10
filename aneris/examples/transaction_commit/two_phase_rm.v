From aneris.aneris_lang.lib Require Export
     assert_proof
     network_util_proof set_proof map_proof nodup_proof coin_flip_proof.
From aneris.examples.transaction_commit Require Import two_phase_prelude.

Section resource_manager.
  Context `{!network_topo}.
  Context `{!anerisG (TC_model RMs) Σ, !tcG Σ}.

  Lemma wp_rm_sendto_aborted st rm ip s h :
    ip_of_address rm = ip →
    s = mkSocket (Some rm) true →
    (st = WORKING ∨ st = PREPARED) →
    rm ∈ RMs →
    inv tcN tc_inv -∗
    tm ⤇ tm_si -∗
    h ↪[ip] s -∗
    pending_discarded -∗
    rm ↦●{1 / 2} st -∗
    WP SendTo #(LitSocket h) #"ABORTED" #tm @[ip] {{ _, True }}.
  Proof.
    iIntros (? -> Hst ?) "#Hinv #Htmsi Hh #Hpend HErm".
    wp_apply (aneris_wp_atomic_take_step_model).
    iInv tcN as (mdl) ">[? HrmI]" "Hclose".
    iModIntro.
    iDestruct (rm_inv_mdl_Exact with "HErm HrmI") as %?; [done|].
    iExists mdl, (<[rm:=ABORTED]> mdl).
    iDestruct (rm_inv_pending_discarded_notcommitted with "HrmI Hpend") as %?.
    iFrame.
    iSplit.
    { iPureIntro. right. destruct Hst; subst; constructor; auto. }
    iDestruct (big_sepS_delete with "HrmI") as "[Hrm HrmI]"; [done|].
    iDestruct "Hrm" as (R T st') "(% & HErm' & _ & Ha & %Hmcoh)".
    simplify_map_eq.
    iCombine "HErm HErm'" as "HErm".
    iMod (mono_mapsto_update _ _  (ABORTED : rm_stateO)
            with "HErm") as "[[HErm HErm'] #Hal]".
    { econstructor; [|reflexivity]. destruct Hst; subst; constructor. }
    wp_apply (aneris_wp_pers_send with "[$Hh $Ha $Htmsi]"); [done..| |].
    { rewrite /tm_si/=. iSplit; [done|]. iNext. auto. }
    iIntros "[Hh Hrm] Hfrag".
    iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists _. iFrame.
    rewrite /rm_inv.
    iApply big_sepS_delete; [done|].
    iSplitL "Hrm HErm' Hpend".
    { iExists _, ({[_]} ∪ _), _. iFrame "∗#".
      rewrite lookup_insert //=.
      iSplit; [done|].
      iPureIntro.
      eapply messages_model_agree_send; [|done|done].
      destruct Hst; simplify_eq; constructor. }
    iApply (big_sepS_impl with "HrmI").
    iIntros "!#" (rm' ?).
    rewrite lookup_insert_ne; [eauto |set_solver].
  Qed.

  Lemma wp_rm_receivefrom rm ip s h :
    ip_of_address rm = ip →
    s = mkSocket (Some rm) true →
    rm ∈ RMs →
    {{{ inv tcN tc_inv ∗ rm ⤇ rm_si ∗ h ↪[ip] s }}}
      ReceiveFrom (# (LitSocket h)) @[ip]
    {{{ m, RET SOMEV (#(m_body m), #(m_sender m)); h ↪[ip] s ∗ rm_si m }}}.
  Proof.
    iIntros (? -> ? Φ) "(#Hinv & #Hrm_si & Hh) HΦ".
    iInv tcN as (?) ">[? HRMs]" "Hclose".
    rewrite /rm_inv (big_sepS_elem_of_acc _ _ rm) //.
    iDestruct "HRMs" as "[Hrm HRMs]".
    iDestruct "Hrm" as (R T st) "(?&?&?& Hrm & %)".
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Hrm $Hrm_si]"); [done..|].
    iIntros (?) "(Hh & Hrm & Hm)".
    iMod ("Hclose" with "[-Hm Hh HΦ]") as "_".
    { iModIntro. iExists _. iFrame.
      iApply "HRMs". iExists _,_,_. by iFrame. }
    iApply "HΦ". eauto.
  Qed.

  Lemma wp_rm_wait_commit_abort_receivefrom ip rm h s :
    ip_of_address rm = ip →
    s = mkSocket (Some rm) true →
    rm ∈ RMs →
    {{{ inv tcN tc_inv ∗ rm ⤇ rm_si ∗ h ↪[ip] s }}}
      wait_receivefrom #(LitSocket h)
        (λ: "m", (Fst "m" = #"COMMIT") || (Fst "m" = #"ABORT"))
    @[ip] {{{ m, RET (#(m_body m), #(m_sender m));
                ⌜m_body m = "COMMIT" ∨ m_body m = "ABORT"⌝ ∗
                h ↪[ip] s ∗ rm_si m }}}.
  Proof.
    iIntros (??? Φ) "(#Hinv & #Hrmsi & Hh) HΦ" .
    rewrite /wait_receivefrom. do 7 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_bind (ReceiveFrom _).
    wp_apply (wp_rm_receivefrom with "[$]"); [done..|].
    iIntros (v) "[Hh Hm]".
    simplify_eq.
    wp_apply wp_unSOME; [done|]. iIntros "_".
    wp_pures.
    case_bool_decide as Heq.
    - wp_pures. inversion Heq.
      iApply "HΦ". auto with iFrame.
    - wp_pures. case_bool_decide as Heq'.
      + wp_pures. inversion Heq'.
        iApply "HΦ". auto with iFrame.
      + wp_if. by wp_apply ("IH" with "Hh").
  Qed.

  (** * Resource manager spec *)
  Lemma resource_manager_spec rm :
    rm ∈ RMs →
    unbound {[rm]} -∗
    inv tcN tc_inv -∗
    rm ⤇ rm_si -∗
    tm ⤇ tm_si -∗
    pending -∗
    rm ↦●{1 / 2} WORKING -∗
    WP resource_manager #rm #tm @[ip_of_address rm] {{ v, True }}.
  Proof.
    iIntros (?) "Hp #Hinv #Hrmsi #Htmsi Hpend HErm".
    rewrite /resource_manager.
    wp_pures. wp_socket h as "Hh". wp_pures. wp_socketbind.
    wp_bind (ReceiveFrom _).
    wp_apply (wp_rm_receivefrom with "[$Hh $Hrmsi $Hinv]"); [done..|].
    iIntros (?) "[Hh Hm]". simplify_eq.
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    iDestruct "Hm" as "[%Heq | [(%Heq & #Hshot & HRMs) | [%Heq Hpend_disc]]]";
      rewrite Heq; last first.
    - (* received "ABORT" *)
      rewrite bool_decide_eq_true_2 //. wp_if.
      wp_apply (wp_rm_sendto_aborted with "Hinv Htmsi Hh Hpend_disc HErm"); auto.
    - (* received "COMMIT"; cannot happen *)
      rewrite (big_sepS_elem_of _ _ rm) //.
      iDestruct (mono_mapsto_related with "HErm HRMs") as %Hrel.
      by apply rm_step_rtc_not_prepared_working in Hrel.
    - (* received "PREPARE" *)
      rewrite bool_decide_eq_false_2 //. wp_if.
      wp_apply coin_flip_spec; [done|].
      iIntros (b) "_".
      destruct b; wp_pures.
      { (* locally decided to abort *)
        iMod (pending_discard with "Hpend") as "#Hpend".
        wp_apply (wp_rm_sendto_aborted with "Hinv Htmsi Hh Hpend HErm"); auto. }
      (* locally preaparing to commit *)
      wp_bind (SendTo _ _ _).
      wp_apply aneris_wp_atomic_take_step_model.
      iInv tcN as (mdl) ">[? HrmI]" "Hclose".
      iModIntro.
      iDestruct (rm_inv_mdl_Exact with "HErm HrmI") as %?; [done|].
      iExists mdl, (<[rm:=PREPARED]> mdl).
      iDestruct (rm_inv_pending_notcommitted with "HrmI Hpend") as %?.
      iFrame.
      iSplit.
      { iPureIntro. right. constructor; auto. }
      iDestruct (big_sepS_delete with "HrmI") as "[Hrm HrmI]"; [done|].
      iDestruct "Hrm" as (R T st) "(% & HErm' & _ & Hrm & %Hmcoh)".
      simplify_map_eq.
      iCombine "HErm HErm'" as "HErm".
      iMod (mono_mapsto_update _  _ (PREPARED : rm_stateO) with "HErm")
        as "[[HErm HErm'] #Hal]".
      { econstructor; [|reflexivity]. constructor. }
      wp_apply (aneris_wp_pers_send with "[$Hh $Hrm $Htmsi Hpend]");
        [done..| |].
      { rewrite /tm_si/=. iSplit; [done|]. iNext. auto. }
      iIntros "[Hh Hrm] Hfrag".
      iMod ("Hclose" with "[Hrm HrmI HErm' Hfrag]") as "_".
      { iModIntro. iExists _. iFrame.
        rewrite /rm_inv.
        iApply big_sepS_delete; [done|].
        iSplitL "Hrm HErm'".
        { iExists _, (_ ∪ _), _. iFrame.
          rewrite lookup_insert //=.
          iSplit; [done|].
          iPureIntro.
          eapply messages_model_agree_send; [|done|done].
          constructor. }
        iApply (big_sepS_impl with "HrmI").
        iIntros "!#" (rm' ?).
        rewrite lookup_insert_ne; [eauto |set_solver]. }
      iModIntro. do 4 wp_pure _.
      wp_apply (wp_rm_wait_commit_abort_receivefrom
                       with "[$Hinv $Hrmsi $Hh]"); [done..|].
      iIntros (v).
      rewrite {2}/rm_si.
      iDestruct 1 as ([-> | ->]) "(Hh & Hm')"; simplify_eq.
      + (* decision to commit *)
        wp_pures.
        iDestruct "Hm'" as "[% | [(_ & #Hshot & Hprepared) | [% _]]]";
          [done| |done].
        wp_apply aneris_wp_atomic_take_step_model.
        iInv tcN as (mdl') ">[? HrmI]" "Hclose".
        iModIntro.
        iDestruct (rm_inv_mdl_Exact with "HErm HrmI") as %?; [done|].
        iExists mdl', (<[rm:=COMMITTED]> mdl').
        iFrame.
        iDestruct (rm_inv_cancommit with "HrmI Hprepared Hshot") as %?.
        iSplit.
        { iPureIntro. right. by constructor. }
        iClear "Hprepared".
        iFrame.
        iDestruct (big_sepS_delete with "HrmI") as "[Hrm HrmI]"; [done|].
        iDestruct "Hrm" as (?? st) "(% & HErm' & _ & Hrm & %Hmcoh')".
        simplify_map_eq.
        iCombine "HErm HErm'" as "HErm".
        iMod (mono_mapsto_update _  _ (COMMITTED : rm_stateO) with "HErm")
          as "[[HErm HErm'] #Hal']".
        { econstructor; [|reflexivity]. constructor. }
        wp_apply (aneris_wp_pers_send with "[$Hh $Hrm $Htmsi]"); [done..| |].
        { rewrite /tm_si/=. iSplit; [done|]. iNext. auto. }
        iIntros "[Hh Hrm] Hfrag".
        iMod ("Hclose" with "[Hrm HrmI HErm' Hfrag]"); [|done].
        iModIntro. iExists _. iFrame.
        rewrite /rm_inv.
        iApply big_sepS_delete; [done|].
        iSplitL "Hrm HErm'".
        { iExists _, (_ ∪ _), _. iFrame. iFrame "#".
          rewrite lookup_insert //=.
          iSplit; [done|].
          iPureIntro.
          eapply messages_model_agree_send; [|done|done].
          constructor. }
        iApply (big_sepS_impl with "HrmI").
        iIntros "!#" (rm' ?).
        rewrite lookup_insert_ne; [eauto |set_solver].
      + (* decision to abort *)
        wp_pures.
        iDestruct "Hm'" as "[% | [[% _] | (% & Hpend_disc)]]"; try done.
        wp_apply (wp_rm_sendto_aborted with "Hinv Htmsi Hh Hpend_disc HErm");
          auto.
  Qed.

End resource_manager.

From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export adequacy.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.prelude Require Import gmultiset.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_events
     state_interp_messages_history.
From trillium.fairness Require Import fairness.
From fairneris Require Import model_draft.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG (fair_model_to_model simple_fair_model) Σ}.

  (* TODO: Move this elsehwere and use it where we now use ad hoc induction *)
  Lemma fupd_elim_laterN E1 E2 n (P:iProp Σ) :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2}▷=>^n |={E2,E1}=> P.
  Proof.
    iIntros (Hle) "HP".
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose".
    iInduction n as [|n] "IHn"; [by iMod "Hclose"|]=> /=.
    iIntros "!>!>!>".
    iApply ("IHn" with "HP Hclose").
  Qed.

  Lemma elem_of_mABn m n : m ∈ mABn n → m = mAB.
  Proof. induction n; set_solver. Qed.

  Lemma elem_of_gset_of_gmultiset_gset `{Countable C} (M : gmultiset C) x :
    x ∈ gset_of_gmultiset M ↔ x ∈ M.
  Proof.
    rewrite /gset_of_gmultiset gmultiset_elem_of_dom. apply elem_of_multiplicity.
  Qed.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iModIntro.
    iIntros (ex atr c lbl σ2 Hexvalid Hex Hstep) "(Hevs & Hsi & % & Hauth)".
    rewrite (last_eq_trace_ends_in ex c); [|done].
    iDestruct "Hsi" as (γm mh)
                         "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh &
                           Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iApply fupd_elim_laterN; [solve_ndisj|].
    destruct c as [tp1 σ1]=> /=.
    rewrite /simple_valid_state_evolution in H.
    rewrite /trace_ends_in in Hex.
    rewrite Hex in H. simpl in *.
    destruct σ1; simpl in *; simplify_eq.
    destruct (trace_last atr) eqn:Hs.
    { destruct H as (_ & Hσ & _).
      inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|σ|σ];
        simplify_eq/=.
      - rewrite /messages_to_receive_at_multi_soup in Hm. set_solver.
      - set_solver.
      - set_solver. }
    (* Sent *)
    - destruct H as (Hsteps & Hσ & H').
      inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|σ|σ];
        simplify_eq/=.
      (* Deliver *)
      + destruct sent;
          [by rewrite /messages_to_receive_at_multi_soup in Hm; set_solver|].
        iExists (Delivered sent 0), (Some Ndeliver).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          rewrite /messages_to_receive_at_multi_soup in Hm.
          assert (m = mAB) as ->.
          { apply elem_of_filter in Hm as [Hdest Hm].
            apply elem_of_gset_of_gmultiset_gset in Hm.
            apply elem_of_mABn in Hm.
            done. }
          assert (a = m_destination mAB) as ->.
          { by apply elem_of_filter in Hm as [-> _]. }
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [multiset_solver|].
          destruct H' as (shA & sh' & H').
          exists shA, sh'.
          assert (state_sockets0 !! ip = Some Sn) as HSn' by eauto.
          apply Hnscoh in HSn as (?&?&?&?&?).
          assert (ip = ip_of_address saB) as ->.
          { eapply H2 in Hsh. eapply Hsh in Hsaddr. done. }
          assert (Sn = {[sh' := (sB, mABm 0)]}) as ->.
          { rewrite H' in HSn'.
            rewrite insert_commute in HSn'; [|done].
            rewrite lookup_insert in HSn'.
            by inversion HSn'. }
          assert (sh = sh') as ->.
          { rewrite lookup_insert_Some in Hsh. set_solver. }
          assert (skt = sB) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          assert (R = []) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          rewrite H'.
          simpl.
          rewrite insert_insert.
          rewrite insert_commute; [|done]. rewrite insert_insert.
          set_solver. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_deliver_message;
            eauto with set_solver. }
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                  eauto using messages_history_coh_deliver_message|].
        iSplitL "Hlcoh";
          [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
        by iApply (free_ips_coh_deliver_message with "Hfreeips").
      (* Dup *)
      + destruct sent as [|sent]; [set_solver|].
        iExists (Sent $ S $ S sent), (Some Ndup).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [done|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_duplicate_message;
            eauto with set_solver.
          by apply gmultiset_singleton_subseteq_l. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_duplicate_message.
      (* Drop *)
      + destruct sent as [|sent]; [by set_solver|].
        iExists (Sent sent), (Some Ndrop).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->. simpl.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [by multiset_solver|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { iPureIntro.
          simplify_eq /=.
          apply (last_eq_trace_ends_in) in Hex as ->.
          rewrite -message_history_evolution_drop_message; first done.
          apply gmultiset_difference_subseteq. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_drop_message.
    (* Delivered *)
    - destruct H as (Hvalid&Hσ&H').
      inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|σ|σ];
        simplify_eq/=.
      (* Deliver *)
      + destruct sent;
          [by rewrite /messages_to_receive_at_multi_soup in Hm; set_solver|].
        iExists (Delivered sent (S delivered)), (Some Ndeliver).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          rewrite /messages_to_receive_at_multi_soup in Hm.
          assert (m = mAB) as ->.
          { apply elem_of_filter in Hm as [_ Hm].
            apply elem_of_gset_of_gmultiset_gset in Hm.
            apply elem_of_mABn in Hm.
            done. }
          assert (a = m_destination mAB) as ->.
          { by apply elem_of_filter in Hm as [-> _]. }
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [multiset_solver|].
          destruct H' as (shA & sh' & H').
          exists shA, sh'.
          assert (state_sockets0 !! ip = Some Sn) as HSn' by eauto.
          apply Hnscoh in HSn as (?&?&?&?&?).
          assert (ip = ip_of_address saB) as ->.
          { eapply H2 in Hsh. eapply Hsh in Hsaddr. done. }
          assert (Sn = {[sh' := (sB, mABm (S delivered))]}) as ->.
          { rewrite H' in HSn'.
            rewrite insert_commute in HSn'; [|done].
            rewrite lookup_insert in HSn'.
            by inversion HSn'. }
          assert (sh = sh') as ->.
          { rewrite lookup_insert_Some in Hsh. set_solver. }
          assert (skt = sB) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          assert (R = mABm (S delivered)) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          rewrite H'.
          simpl.
          rewrite insert_insert.
          rewrite insert_commute; [|done]. rewrite insert_insert. 
          set_solver. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_deliver_message;
            eauto with set_solver. }
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                  eauto using messages_history_coh_deliver_message|].
        iSplitL "Hlcoh";
          [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
        by iApply (free_ips_coh_deliver_message with "Hfreeips").
      (* Dup *)
      + destruct sent as [|sent]; [set_solver|].
        iExists (Delivered (S $ S sent) delivered), (Some Ndup).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [done|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_duplicate_message;
            eauto with set_solver.
          by apply gmultiset_singleton_subseteq_l. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_duplicate_message.
      (* Drop *)
      + destruct sent as [|sent]; [by set_solver|].
        iExists (Delivered sent delivered), (Some Ndrop).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->. simpl.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [by multiset_solver|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { iPureIntro.
          simplify_eq /=.
          apply (last_eq_trace_ends_in) in Hex as ->.
          rewrite -message_history_evolution_drop_message; first done.
          apply gmultiset_difference_subseteq. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_drop_message.
    (* Delivered *)
    - destruct H as (Hvalid&Hσ&H').
      inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|σ|σ];
        simplify_eq/=.
      (* Deliver *)
      + destruct sent as [|sent];
          [by rewrite /messages_to_receive_at_multi_soup in Hm; set_solver|].
        iExists (Received sent (S delivered)), (Some Ndeliver).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          rewrite /messages_to_receive_at_multi_soup in Hm.
          assert (m = mAB) as ->.
          { apply elem_of_filter in Hm as [Hdest Hm].
            apply elem_of_gset_of_gmultiset_gset in Hm.
            apply elem_of_mABn in Hm.
            done. }
          assert (a = m_destination mAB) as ->.
          { by apply elem_of_filter in Hm as [-> _]. }
          simpl.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [multiset_solver|].
          destruct H' as (shA & sh' & H').
          exists shA, sh'.
          assert (state_sockets0 !! ip = Some Sn) as HSn' by eauto.
          apply Hnscoh in HSn as (?&?&?&?&?).
          assert (ip = ip_of_address saB) as ->.
          { eapply H2 in Hsh. eapply Hsh in Hsaddr. done. }
          assert (Sn = {[sh' := (sB, mABm delivered)]}) as ->.
          { rewrite H' in HSn'.
            rewrite insert_commute in HSn'; [|done].
            rewrite lookup_insert in HSn'.
            by inversion HSn'. }
          assert (sh = sh') as ->.
          { rewrite lookup_insert_Some in Hsh. set_solver. }
          assert (skt = sB) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          assert (R = mABm delivered) as ->.
          { rewrite lookup_insert in Hsh. set_solver. }
          rewrite H'.
          simpl.
          rewrite insert_insert.
          rewrite insert_commute; [|done]. rewrite insert_insert. 
          set_solver. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_deliver_message;
            eauto with set_solver. }
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                  eauto using messages_history_coh_deliver_message|].
        iSplitL "Hlcoh";
          [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
        by iApply (free_ips_coh_deliver_message with "Hfreeips").
      (* Dup *)
      + destruct sent as [|sent]; [set_solver|].
        iExists (Received (S $ S sent) delivered), (Some Ndup).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [done|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_duplicate_message;
            eauto with set_solver.
          by apply gmultiset_singleton_subseteq_l. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_duplicate_message.
      (* Drop *)
      + destruct sent as [|sent]; [by set_solver|].
        iExists (Received sent delivered), (Some Ndrop).
        rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
          [| |done|done]; last first.
        { econstructor; [done| |done]. econstructor 2; eauto. }
        iFrame "Hevs Hauth Hsi".
        iSplit; last first.
        { iPureIntro.
          rewrite /simple_valid_state_evolution.
          apply elem_of_mABn in H as ->. simpl.
          split; [econstructor; [apply Hs|econstructor|done]|].
          split; [by multiset_solver|done]. }
        iExists γm, mh. iFrame.
        iSplit.
        { iPureIntro.
          simplify_eq /=.
          apply (last_eq_trace_ends_in) in Hex as ->.
          rewrite -message_history_evolution_drop_message; first done.
          apply gmultiset_difference_subseteq. }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. by apply messages_history_coh_drop_message.
  Qed.

End state_interpretation.

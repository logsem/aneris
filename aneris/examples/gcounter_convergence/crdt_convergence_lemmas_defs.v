From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.prelude Require Import gset_map list time.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import network resources proofmode adequacy.
From aneris.aneris_lang.lib Require Import list_proof vector_clock_proof.
From aneris.examples.gcounter_convergence Require Import
     crdt_model crdt_resources crdt_proof crdt_main_rel crdt_runner vc.
From trillium.traces Require Import trace_properties.
From RecordUpdate Require Import RecordSet.

Import RecordSetNotations.

Section crdt_convergence_lemmas.
  Context {gcdata : GCData} (ps : programs_using_gcounters gcdata).

  Notation ith_sa i := (gcd_addr_list gcdata !!! i).

  Lemma is_send_op_dec (e : expr) :
    {esmt : (socket_handle * (string * socket_address)) |
      e = SendTo #(LitSocket esmt.1) #esmt.2.1 #esmt.2.2} +
    {∀ (sh : socket_handle) (msg : string) (to : socket_address),
        e ≠ SendTo #(LitSocket sh) #msg #to}.
  Proof.
    destruct e as [| | | | | | | | | | | | | | | | | | | | | | | | |esh emsg eto| | | | |];
      (try by right; intros ? ? ? Hns; simplify_eq); [].
    destruct esh as [[[]| | | |]| | | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
      (try by right; intros ? ? ? Hns; simplify_eq); [].
    destruct emsg as [[[]| | | |]| | | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
      (try by right; intros ? ? ? Hns; simplify_eq); [].
    destruct eto as [[[]| | | |]| | | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
      (try by right; intros ? ? ? Hns; simplify_eq); [].
    left; eexists (_, (_, _)); done.
  Qed.

  Lemma message_in_soup (r : message_soup) mbody from :
    {m | m ∈ r ∧ m_body m = mbody ∧ m_sender m = from} +
    {∀ m, m ∈ r → m_body m = mbody → m_sender m = from → False}.
  Proof.
    remember (elements r) as l; symmetry in Heql.
    assert (elements r ≡ₚ l) as Hrl by by rewrite Heql.
    clear Heql.
    revert r Hrl.
    induction l as [|m l IHl]; intros r Hrl.
    - symmetry in Hrl; apply Permutation_nil in Hrl.
      apply elements_empty_inv, leibniz_equiv in Hrl as ->.
      right; set_solver.
    - assert (elements (r ∖ {[m]}) ≡ₚ l) as Hrdiff.
      { apply NoDup_Permutation.
        - apply NoDup_elements.
        - eapply NoDup_cons.
          erewrite <- Hrl.
          apply NoDup_elements.
        - intros x; rewrite elem_of_elements elem_of_difference.
          split.
          + rewrite -elem_of_elements Hrl elem_of_cons elem_of_singleton; set_solver.
          + intros Hl; split.
            * rewrite -elem_of_elements Hrl elem_of_cons; eauto.
            * assert (NoDup (m :: l)) as [? ?]%NoDup_cons by by rewrite -Hrl; apply NoDup_elements.
              rewrite elem_of_singleton; intros ->; done. }
      destruct (IHl (r ∖ {[m]})) as [(m' & Hm'1 & Hm'2 & Hm'3)|Hnm']; first done.
      { left; exists m'; split_and!; [set_solver|done|done]. }
      destruct (decide (m_body m = mbody)); last first.
      { right.
        intros m' Hm'1%elem_of_elements Hm'2 Hm'3.
        rewrite -> Hrl in Hm'1.
        apply elem_of_cons in Hm'1 as [?|Hm'1]; first by simplify_eq.
        rewrite <- Hrdiff, elem_of_elements in Hm'1.
        eapply Hnm'; eauto. }
      destruct (decide (m_sender m = from)); last first.
      { right.
        intros m' Hm'1%elem_of_elements Hm'2 Hm'3.
        rewrite -> Hrl in Hm'1.
        apply elem_of_cons in Hm'1 as [?|Hm'1]; first by simplify_eq.
        rewrite <- Hrdiff, elem_of_elements in Hm'1.
        eapply Hnm'; eauto. }
      left; exists m; split_and!; [|done|done].
      rewrite -elem_of_elements Hrl elem_of_cons; eauto.
  Qed.

  Definition is_send_msg (i j : nat) (mbody : string) (ev : EventObservation aneris_lang) : Prop :=
    ∃ (sh: socket_handle) (from to: socket_address) skts skt r,
      gcd_addr_list gcdata !! i = Some from ∧
      gcd_addr_list gcdata !! j = Some to ∧
      ev.(pre_state).(state_sockets) !! (ip_of_address from) = Some skts ∧
      skts !! sh = Some (skt, r) ∧
      saddress skt = Some from ∧
      ev.(pre_expr) = (mkExpr (ip_of_address from) (SendTo #(LitSocket sh) #mbody #to)) ∧
      ev.(post_expr) = (mkExpr (ip_of_address from) #(String.length mbody)) ∧
      ev.(post_state) = ev.(pre_state)
                             <| state_ms := {[+ mkMessage from to mbody +]}
                                              ⊎ ev.(pre_state).(state_ms) |>.

  Definition is_send (i j : nat) (ev : EventObservation aneris_lang) : Prop :=
    ∃ msg, is_send_msg i j msg ev.

  Global Instance is_send_dec i j ev: Decision (is_send i j ev).
  Proof.
    destruct ev as [e σ e' σ'].
    destruct (gcd_addr_list gcdata !! i) as [from|] eqn:Hfrom; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (gcd_addr_list gcdata !! j) as [to|] eqn:Hto; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (σ.(state_sockets) !! (ip_of_address from)) as [skts|] eqn:Hskts; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct e as [eip e].
    destruct (decide (eip = ip_of_address from)) as [Heip|]; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (is_send_op_dec e) as [[(sh&mbody&to') ->]|Hns]; simpl; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. eapply Hns; eauto. }
    destruct (decide (to' = to)) as [->|]; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (decide (e' = (mkExpr (ip_of_address from) #(String.length mbody)))) as [->|];
      last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (skts !! sh) as [[skt r]|] eqn:Hsktssh; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (decide (σ' = σ <| state_ms := {[+ mkMessage from to mbody +]}
                                            ⊎ σ.(state_ms) |>)) as [->|]; last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    destruct (decide (saddress skt = Some from)); last first.
    { right; intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=. }
    simplify_eq.
    left; eexists _, _, _, _, _, _, _; simpl; eauto 10.
  Qed.

  Definition is_receive_msg (i j : nat) (mbody : string) (ev : EventObservation aneris_lang) : Prop :=
    ∃ (sh: socket_handle) from to skts skt r m,
      gcd_addr_list gcdata !! i = Some to ∧
      gcd_addr_list gcdata !! j = Some from ∧
      ev.(pre_state).(state_sockets) !! (ip_of_address to) = Some skts ∧
      skts !! sh = Some (skt, r ++ [m]) ∧
      saddress skt = Some to ∧
      m_body m = mbody ∧
      m_sender m = from ∧
      ev.(pre_expr) = (mkExpr (ip_of_address to) (ReceiveFrom #(LitSocket sh))) ∧
      ev.(post_expr) = (mkExpr (ip_of_address to) (SOMEV (#(m_body m),#(m_sender m)))) ∧
      ev.(post_state) = ev.(pre_state) <| state_sockets :=
      <[(ip_of_address to):= <[sh := (skt, r)]>skts]> ev.(pre_state).(state_sockets) |>.

  (** It is always the case that for any [i] and [j] (not the same as [i]), for any n, the number *)
  (** of messages sent from node [i] to node [j] is greater than of equal to [n]. *)
  Definition network_fairness_always_sending
             (ex : execution_trace aneris_lang)
             (iex : inf_execution_trace aneris_lang) : Prop :=
    always
      (λ ex' iex',
       ∀ i j n,
         i < GClen gcdata →
         j < GClen gcdata →
         i ≠ j →
         eventually
           (λ ex'' iex'',
            n ≤ length (filter (is_send i j) (events_of_trace (sendonEV (ith_sa i)) ex'')))
           ex' iex')
      ex iex.

  (** It is always the case that for any [i] and any [n], the number of messages received by node *)
  (** [i] is greater than or equal to [n]. *)
  Definition network_fairness_always_receiving
             (ex : execution_trace aneris_lang)
             (iex : inf_execution_trace aneris_lang) : Prop :=
    always
      (λ ex' iex',
       ∀ i n,
         eventually
           (λ ex'' iex'',
            n ≤ length (events_of_trace (receiveonEV (ith_sa i)) ex'')) ex' iex')
      ex iex.

  (** It is always the case that any message ev if ev is sent from node [i] to node [j] within *)
  (** [k] steps then there is some [n] such that after [n + k] steps the message [ev'] with *)
  (** message body [msg] is sent after [ev] and is also received at node [j]. *)
  Definition network_sent_received_fairness
             (ex : execution_trace aneris_lang)
             (iex : inf_execution_trace aneris_lang) : Prop :=
    always
      (λ ex' iex',
       ∀ i j k s ev,
         i < GClen gcdata →
         j < GClen gcdata →
         i ≠ j →
         events_of_trace (sendonEV (ith_sa i)) (ex' +trl+ (inflist_take k iex')) !! s = Some ev →
         is_send i j ev →
         ∃ n s' msg ev' ev'',
           s ≤ s' ∧
           events_of_trace (sendonEV (ith_sa i)) (ex' +trl+ (inflist_take (n + k) iex')) !! s'
           = Some ev' ∧ is_send_msg i j msg ev' ∧
           ev'' ∈ events_of_trace (receiveonEV (ith_sa j)) (ex' +trl+ (inflist_take (n + k) iex')) ∧
           is_receive_msg j i msg ev'')
      ex iex.

  (** The system has reached a stability point [vc] if the from now on the value stored on [i]th *)
  (** component of the [i]th node agrees with [vc]. *)
  Definition stability_reached
             (locs : list loc)
             (vc : vector_clock (GClen gcdata))
             (ex : execution_trace aneris_lang)
             (iex : inf_execution_trace aneris_lang) : Prop :=
    always (λ ex' iex',
            ∀ i : fin (GClen gcdata),
              ∃ h (vc' : vector_clock (GClen gcdata)),
                (trace_last ex').2.(state_heaps)
                  !! (ip_of_address (gcd_addr_list gcdata !!! (fin_to_nat i))) = Some h ∧
                h !! (locs !!! (fin_to_nat i)) = Some (vector_clock_to_val vc') ∧
                vc' !!! i = vc !!! i
           ) ex iex.

  (** The system has reached the convergence point [vc] if all nodes agree on [vc] as the values *)
  (** of the distributed counter.*)
  Definition convergence_point_reached
             (locs : list loc)
             (vc : vector_clock (GClen gcdata))
             (ex : execution_trace aneris_lang)
             (iex : inf_execution_trace aneris_lang) : Prop :=
    always (λ ex' iex',
            ∀ i : fin (GClen gcdata),
              ∃ h, (trace_last ex').2.(state_heaps)
                     !! (ip_of_address (gcd_addr_list gcdata !!! (fin_to_nat i))) = Some h ∧
                   h !! (locs !!! (fin_to_nat i)) = Some (vector_clock_to_val vc)) ex iex.

  Lemma closed_model_relation_network_fair_fair_model_main locs ex iex mtr imtr i j :
    length locs = GClen gcdata →
    valid_inf_exec ex iex →
    closed_model_relation gcdata locs ex mtr iex imtr →
    network_fairness_always_sending ex iex →
    network_fairness_always_receiving ex iex →
    network_sent_received_fairness ex iex →
    will_be_merged_ij i j mtr imtr.
  Proof.
    intros Hvex Hlen Hcmrel Has Har Hsr.
    destruct (decide (i = j)) as [->|Hneq].
    { apply holds_eventually; done. }
    assert (fin_to_nat i ≠ fin_to_nat j) as Hneq'.
    { intros ?; apply Hneq; apply fin_to_nat_inj; done. }
    assert (∃ h,
            (trace_last ex).2.(state_heaps) !! (ip_of_address (ith_sa (fin_to_nat i))) = Some h ∧
            h !! (locs !!! (fin_to_nat i)) =
            Some (vector_clock_to_val (vec_to_list (trace_last mtr !!! i))))
      as [h [Hh Hhl]].
    { destruct Hcmrel as [_ Hcmrel%always2_holds].
      destruct Hcmrel as (_&Hvrel&_&_).
      apply Hvrel. }
    remember (length (filter (is_send (fin_to_nat i) (fin_to_nat j))
                             (events_of_trace (sendonEV (ith_sa (fin_to_nat i))) ex))) as k.
    pose proof (always_holds _ _ _ Has (fin_to_nat i) (fin_to_nat j) (k + 2)
                             (fin_to_nat_lt _) (fin_to_nat_lt _) Hneq') as Hevs.
    apply eventually_take_drop in Hevs as [ns Hevs].
    edestruct (events_of_trace_app_map (sendonEV (ith_sa (fin_to_nat i))) ex (inflist_take ns iex))
        as (psevs & Hsevlen & Happ & Hpsevsin).
    { eapply valid_inf_exe_valid_exec, valid_inf_exe_take_drop; done. }
    rewrite Happ in Hevs.
    rewrite filter_app app_length -Heqk in Hevs.
    pose proof Hcmrel as [Hgms _].
    destruct (filter (is_send i j) psevs) as [|ev [|ev' fpsev]] eqn:Hfpsevs;
      [by simpl in *; lia|by simpl in *; lia|].
    apply filter_list_extract_first2 in Hfpsevs as (z1 & z2 & Hz12 & Hz1 & Hz2 & Hev & Hev').
    assert (ev ∈ psevs) as Hevin.
    { apply elem_of_list_lookup; eauto. }
    assert (ev' ∈ psevs) as Hev'in.
    { apply elem_of_list_lookup; eauto. }
    destruct (Hpsevsin ev Hevin) as (z1' & c1 & c2 & Hc1 & Hc2 & Htrgd).
    apply (always_unroll_n _ ns), always_holds in Hgms.
    destruct Hgms as (? & <-%trace_append_list_inj2 &Hgms).
    specialize (Hgms 0 z1' _ _ (Nat.le_0_l _) eq_refl Hc1).
    assert (∃ h' (vc : vector_clock (GClen gcdata)),
               c1.2.(state_heaps) !! ip_of_address (ith_sa (fin_to_nat i)) = Some h' ∧
               h' !! (locs !!! (fin_to_nat i)) = Some (vector_clock_to_val (vec_to_list vc)) ∧
               vc_le (trace_last mtr !!! i) vc) as (h' & vc & Hh' & Hvc & Hvcle).
    { destruct Hgms as [<-|Hgms].
      - eexists _, _; split_and!; [done|done|reflexivity].
      - destruct (Hgms (fin_to_nat i) (fin_to_nat_lt _)) as (h1&h'&vc1&vc2&Hh1&Hh'&Hvc1&Hvc2&Hvcs).
        rewrite Hh in Hh1; simplify_eq.
        match goal with
          Hvcs : _ =  _ |- _ =>
          apply vec_to_list_inj2 in Hvcs; simplify_eq
        end.
        eauto. }
    apply always_holds in Hsr.
    specialize (Hsr _ _ ns (length (events_of_trace (sendonEV (ith_sa (fin_to_nat i))) ex) + z2)
                    ev' (fin_to_nat_lt i) (fin_to_nat_lt j) Hneq').
    rewrite Happ lookup_app_r in Hsr; last lia.
    rewrite Nat.add_comm Nat.add_sub in Hsr.
    specialize (Hsr Hz2 Hev')
      as (nss & zss & msg & evss & evr & Hz'zss & Hssevs & Hssismsg & Hevr & Hevrirmsg).
    assert (∃ vc' : vector_clock (GClen gcdata),
               vc_is_ser (vector_clock_to_val (vec_to_list vc')) msg ∧ vc_le vc vc')
      as (vc' & Hvc'ser & Hvcvc').
    { pose proof Hcmrel as [_ Hcmrel'].
      apply (always2_unroll_n _ (nss + ns)), always2_holds in Hcmrel'.
      destruct Hcmrel' as (_&_&Hsendrel&_).
      destruct Hsendrel as [sevss [Hsevsslen Hsevss]].
      specialize (Hsevss (fin_to_nat i) (fin_to_nat_lt _)) as (sevs & Hsevs & Hsevsvl & Hsevcorr).
      rewrite (Nat.add_comm nss) inflist_take_add -trace_append_list_assoc in Hsevcorr Hssevs.
      destruct (events_of_trace_app (sendonEV (ith_sa (fin_to_nat i))) (ex +trl+ inflist_take ns iex)
                                    (inflist_take nss (inflist_drop ns iex)))
        as (psevs' & Hsevlen' & Happ' & Hpsevsin').
      { eapply valid_inf_exe_valid_exec; do 2 apply valid_inf_exe_take_drop; done. }
      rewrite Happ' Happ in Hsevcorr Hssevs.
      destruct (Forall2_lookup_l _ _ _ _ _ Hsevcorr Hssevs) as (sinf2 & Hsinf2 & Hcorr2).
      destruct Hcorr2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct Hssismsg as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=.
      destruct (Forall2_lookup_l
                  _ _ _ (length (events_of_trace (sendonEV (ith_sa (fin_to_nat i))) ex) + z1)
                  ev Hsevcorr) as (sinf1 & Hsinf1 & Hcorr1).
      { assert (z1 < length psevs) by by eapply lookup_lt_Some; eauto.
        rewrite lookup_app_l; last by rewrite !app_length; lia.
        rewrite lookup_app_r; last lia.
        rewrite Nat.add_comm Nat.add_sub; done. }
      destruct Hcorr1 as (?&?&?&?&?&?&?&?&?&?&?&?&Hheap&?).
      destruct Hev as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct Hev' as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct Htrgd as (?&?&?&?&?&?&?&?).
      simplify_eq/=.
      match goal with
        Hvcs : _ =  _ |- _ =>
        apply vec_to_list_inj2 in Hvcs; simplify_eq
      end.
      assert (sinf1.1 = sinf2.1).
      { eapply NoDup_lookup; eauto using gcd_addr_list_NoDup. }
      assert (length (events_of_trace (sendonEV (ith_sa (fin_to_nat i))) ex) + z1 < zss)
        as Hlt by lia.
      specialize (Hsevsvl _ _ _ _ Hsinf2 Hlt Hsinf1).
      eexists _; split; first eassumption; eauto. }
    apply (always_unroll_n _ (nss + ns)), always_holds in Har.
    specialize (Har (fin_to_nat j)
                    (S (length (events_of_trace
                                  (receiveonEV (ith_sa (fin_to_nat j)))
                                  (ex +trl+ inflist_take (nss + ns) iex))))).
    apply eventually_take_drop in Har as [nr Hnr].
    rewrite trace_append_list_assoc -inflist_take_add in Hnr.
    assert
      (∃ h'' (vc'' : vector_clock (GClen gcdata)),
          (trace_last (ex +trl+ inflist_take (nss + ns + nr) iex)).2.(state_heaps)
            !! ip_of_address (ith_sa (fin_to_nat j)) = Some h'' ∧
            h'' !! (locs !!! (fin_to_nat j)) = Some (vector_clock_to_val (vec_to_list vc'')) ∧
            vc_le vc' vc'') as (h'' & vc'' & Hh'' & Hvc'' & Hvc'vc'').
    { pose proof Hcmrel as [_ Hcmrel'].
      apply (always2_unroll_n _ (nss + ns + nr)), always2_holds in Hcmrel'.
      destruct Hcmrel' as (_&_&_&Hrec).
      destruct Hrec as [revss [Hsrvsslen Hrevss]].
      specialize (Hrevss _ (fin_to_nat_lt j))
        as (revs & Hrevslen & Hrcorr & h'' & vc'' & Hh'' & Hvc'' & Hle).
      eexists h'', vc''; split_and!; [done|done|].
      rewrite inflist_take_add -trace_append_list_assoc in Hrcorr.
      apply elem_of_list_lookup in Hevr as [zr Hevr].
      destruct (events_of_trace_app
                  (receiveonEV (ith_sa (fin_to_nat j))) (ex +trl+ inflist_take (nss + ns) iex)
                  (inflist_take nr (inflist_drop (nss + ns) iex)))
        as (psevs' & Hsevlen' & Happ' & Hpsevsin').
      { eapply valid_inf_exe_valid_exec; do 2 apply valid_inf_exe_take_drop; done. }
      rewrite Happ' in Hrcorr.
      destruct (Forall2_lookup_l _ _ _ zr evr Hrcorr) as (vc3 & Hvc31 & Hvc3corr).
      { rewrite lookup_app_l; last by eapply lookup_lt_Some; eauto. done. }
      destruct Hvc3corr as (?&?&?&?&?&?&?&(?&?&?)&?).
      destruct Hevrirmsg as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      simplify_eq/=.
      assert (vc3 = vc') as ->.
      { apply vec_to_list_inj2, vector_clock_to_val_inj. eapply vc_is_ser_inj; eauto. }
      eapply Hle; last done.
      apply Forall2_length in Hrcorr.
      rewrite -Happ' trace_append_list_assoc -inflist_take_add in Hrcorr.
      apply lookup_lt_Some in Hevr.
      lia. }
    apply eventually_take_drop.
    exists (nss + ns + nr).
    destruct Hcmrel as [_ Hcmrel'].
    apply (always2_unroll_n _ (nss + ns + nr)), always2_holds in Hcmrel'.
    destruct Hcmrel' as (_&Hvrel&_&_).
    destruct (Hvrel j) as (h3&Hh3&Hlastvc).
    rewrite Hh'' in Hh3; simplify_eq.
    match goal with
      Hvcs :  _ = _ |- _ =>
      apply vec_to_list_inj2 in Hvcs; simplify_eq
    end.
    repeat (etrans; first eassumption; try eassumption).
  Qed.

  Lemma closed_model_relation_network_fair_fair_model locs ex iex mtr imtr :
    length locs = GClen gcdata →
    valid_inf_exec ex iex →
    eventually2 (closed_model_relation gcdata locs) ex mtr iex imtr →
    network_fairness_always_sending ex iex →
    network_fairness_always_receiving ex iex →
    network_sent_received_fairness ex iex →
    eventually fair_model_trace mtr imtr.
  Proof.
    intros Hlen Hvl Hev Hnfs Hnfr Hnfsr.
    apply eventually2_take_drop in Hev as [n [Hev Hevlen]].
    apply eventually_take_drop.
    exists n.
    intros i j.
    apply always_take_drop; intros k.
    eapply (closed_model_relation_network_fair_fair_model_main locs).
    - done.
    - eapply (valid_inf_exe_take_drop _ _ k).
      eapply (valid_inf_exe_take_drop _ _ n).
      exact Hvl.
    - split.
      + apply monotone_from_now_on_unroll_n; apply Hev.
      + apply always2_unroll_n, Hev.
    - do 2 apply always_unroll_n; done.
    - do 2 apply always_unroll_n; done.
    - do 2 apply always_unroll_n; done.
  Qed.

  Lemma closed_model_relation_valid_model_trace locs ex iex mtr imtr :
    eventually2 (closed_model_relation gcdata locs) ex mtr iex imtr →
    eventually valid_model_trace mtr imtr.
  Proof.
    intros Hev.
    apply eventually2_take_drop in Hev as [n Hev].
    apply eventually_take_drop.
    exists n.
    apply always_take_drop; intros k.
    destruct Hev as [[_ Hev] _].
    apply (always2_unroll_n _ k), always2_holds in Hev.
    destruct Hev as [hev _]; done.
  Qed.

  Lemma closed_model_relation_stability_point_transfer vc locs ex iex mtr imtr :
    eventually2 (closed_model_relation gcdata locs) ex mtr iex imtr →
    eventually (stability_reached locs vc) ex iex →
    eventually (stability_point_is_reached vc) mtr imtr.
  Proof.
    intros Hev1 Hev2.
    assert
      (eventually2
         (λ ex' mtr' iex' imtr',
          (always2
             (λ ex'' _ _ _,
              ∀ i : fin (GClen gcdata),
                ∃ h (vc' : vector_clock (GClen gcdata)),
                  (trace_last ex'').2.(state_heaps)
                    !! (ip_of_address (gcd_addr_list gcdata !!! (fin_to_nat i))) = Some h ∧
                  h !! (locs !!! (fin_to_nat i)) = Some (vector_clock_to_val vc') ∧
                  vc' !!! i = vc !!! i) ex' mtr' iex' imtr')) ex mtr iex imtr) as Hev2'.
    { apply eventually_take_drop in Hev2 as [n Hev2].
      apply eventually2_take_drop; exists n; split; last by eapply eventually2_inflist_same_length.
      apply always2_take_drop; intros m.
      split; last first.
      { eapply inflist_same_length_drop, eventually2_inflist_same_length; eauto. }
      apply (always_unroll_n _ m), always_holds in Hev2; done. }
    apply (eventually2_mono _ (always2 (crdt_main_rel_locs_resolved gcdata locs))) in Hev1;
      last first.
    { intros ???? [_ ?]; done. }
    pose proof (eventually2_always2_combine _ _ _ _ _ _ Hev1 Hev2') as Hev.
    clear -Hev.
    apply eventually2_take_drop in Hev as [n [[Hev1 Hev2] Hlen]].
    apply eventually_take_drop.
    exists n.
    apply always_take_drop; intros m.
    apply (always2_unroll_n _ m), always2_holds in Hev1, Hev2.
    intros i.
    destruct Hev1 as (_ & Hvrel & _).
    specialize (Hvrel i) as (h & Hh & Hhv).
    specialize (Hev2 i) as (h' & vc' & Hh' & Hvc' & <-).
    rewrite Hh in Hh'; simplify_eq.
    match goal with
      Hvcs : _ =  _ |- _ =>
      apply vec_to_list_inj2 in Hvcs; simplify_eq
    end; done.
  Qed.

  Lemma closed_model_relation_convergence_point_transfer vc locs ex iex mtr imtr :
    eventually2 (closed_model_relation gcdata locs) ex mtr iex imtr →
    eventually (convergence_point_is_reached vc) mtr imtr →
    eventually (convergence_point_reached locs vc) ex iex.
  Proof.
    intros Hev1 Hev2.
    assert
      (eventually2
         (λ ex' mtr' iex' imtr',
          (always2 (λ _ mtr'' _ imtr'', has_converged_to vc mtr'' imtr'') ex' mtr' iex' imtr'))
         ex mtr iex imtr) as Hev2'.
    { apply eventually_take_drop in Hev2 as [n Hev2].
      apply eventually2_take_drop; exists n; split; last by eapply eventually2_inflist_same_length.
      apply always2_take_drop; intros m.
      split; last first.
      { eapply inflist_same_length_drop, eventually2_inflist_same_length; eauto. }
      apply (always_unroll_n _ m), always_holds in Hev2; done. }
    apply (eventually2_mono _ (always2 (crdt_main_rel_locs_resolved gcdata locs))) in Hev1;
      last first.
    { intros ???? [_ ?]; done. }
    pose proof (eventually2_always2_combine _ _ _ _ _ _ Hev1 Hev2') as Hev.
    clear -Hev.
    apply eventually2_take_drop in Hev as [n [[Hev1 Hev2] Hlen]].
    apply eventually_take_drop.
    exists n.
    apply always_take_drop; intros m.
    apply (always2_unroll_n _ m), always2_holds in Hev1, Hev2.
    intros i.
    destruct Hev1 as (_ & Hvrel & _).
    specialize (Hvrel i) as (h & Hh & Hhv).
    specialize (Hev2 i); simplify_eq; eauto.
  Qed.

  Lemma network_fairness_always_sending_eventually_sends ex iex :
    1 < GClen gcdata →
    network_fairness_always_sending ex iex →
    (∀ i, i < GClen gcdata →
          eventually (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []) ex iex).
  Proof.
    intros Hnnodes Hfs i Hi.
    apply always_holds in Hfs.
    assert (∃ j, i ≠ j ∧ j < GClen gcdata) as [j [Hij Hj]].
    { destruct i.
      - exists 1; done.
      - exists 0; auto with lia. }
    specialize (Hfs i j 1 Hi Hj Hij).
    eapply eventually_mono; last by apply Hfs.
    simpl; clear; intros ex iex Hex.
    destruct (events_of_trace (sendonEV (ith_sa i)) ex); last done.
    simpl in *; lia.
  Qed.

End crdt_convergence_lemmas.

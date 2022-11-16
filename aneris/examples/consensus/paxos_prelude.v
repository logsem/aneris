From stdpp Require Export base fin_maps gmap propset finite.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Export auth.
From iris.base_logic.lib Require Export invariants.
From aneris.prelude Require Export gset_map sig_gset quorum strings.
From aneris.algebra Require Export ballot.
From aneris.lib Require Export gen_heap_light.
From aneris.aneris_lang Require Export tactics proofmode network.
From aneris.aneris_lang.lib Require Export pers_socket_proto inject.
From aneris.aneris_lang.lib Require Export network_util_proof set_proof.
From aneris.aneris_lang.lib.serialization Require Export serialization_proof.
From aneris.examples.consensus Require Export paxos_code paxos_model.
From RecordUpdate Require Export RecordSet.
Import RecordSetNotations.

Open Scope nat_scope.

Class network_topo := {
  Acceptors : gset socket_address;
  Proposers : gset socket_address;
  Learners  : gset socket_address;
  Values : gset Z;

  Acceptors_size_nonzero   : size Acceptors ≠ 0;
  Proposers_size_nonzero   : size Proposers ≠ 0;
  Proposers_Acceptors_disj : Proposers ∩ Acceptors = ∅;
  Learners_size_nonzero    : size Learners ≠ 0;
}.

Instance paxos_majority (topo : network_topo) : PaxosParams socket_address Z :=
  Build_PaxosParams _ _ _ _ _ _ Acceptors (Quorum_majority Acceptors) Values.

Definition Paxos_model (topo : network_topo) : resources.Model :=
  model _ (PNext (params := paxos_majority topo)) PInit.

Instance model_inhabited (topo : network_topo) :
  Inhabited (Paxos_model topo) := populate PInit.

Definition Proposer `{network_topo} := sig_gset Proposers.
Definition Learner `{network_topo} := sig_gset Learners.

Definition ValueO `{network_topo} := sigO (λ v, v ∈ Values).

Class paxosPreG Σ (topo : network_topo) := {
  paxos_messages_inPreG :> inG Σ (authUR (gsetUR Message));
  paxos_ballot_inPreG :> inG Σ (ballot_oneshotUR ValueO);
  paxos_maxBal_heap_inPreG :> inG Σ (authUR (gen_heapUR Acceptor (option Ballot)));
  paxos_maxVal_heap_inPreG :> inG Σ (authUR (gen_heapUR Acceptor (option (Ballot * Value))));
}.
Definition paxosΣ (topo : network_topo) : gFunctors :=
  #[GFunctor (authUR (gsetUR Message));
    GFunctor (ballot_oneshotUR ValueO);
    GFunctor (authUR (gen_heapUR Acceptor (option Ballot)));
    GFunctor (authUR (gen_heapUR Acceptor (option (Ballot * Value))))
   ].

Instance subG_paxosΣ {Σ} {topo : network_topo} :
  subG (paxosΣ topo) Σ → paxosPreG Σ topo.
Proof. solve_inG. Qed.

Class paxosG Σ (topo : network_topo) := {
  paxos_messages :> inG Σ (authUR (gsetUR Message));
  paxos_messages_gname : gname;

  paxos_ballot :> inG Σ (ballot_oneshotUR ValueO);
  paxos_ballot_gname : gname;

  paxos_maxBal_heap_inG :> inG Σ (authUR (gen_heapUR Acceptor (option Ballot)));
  paxos_maxBal_gname : gname;

  paxos_maxVal_heap_inG :> inG Σ (authUR (gen_heapUR Acceptor (option (Ballot * Value))));
  paxos_maxVal_gname : gname;
}.

Section paxos_prelude.
  Context `{topo: !network_topo}.
  Context `{!paxosG Σ topo}.
  Context `{!anerisG (Paxos_model topo) Σ}.

  Lemma proposer_not_acceptor p :
    p ∈ Proposers → p ∉ Acceptors.
  Proof. pose proof Proposers_Acceptors_disj; set_solver. Qed.

  Lemma acceptor_not_proposer a :
    a ∈ Acceptors → a ∉ Proposers.
  Proof. pose proof Proposers_Acceptors_disj; set_solver. Qed.

  Lemma majority_show_quorum Q :
    size Q > size Acceptors / 2 → QuorumA Q.
  Proof.
    intros. constructor.
    - rewrite gset_map_size //.
    - apply sig_gset_map_proj1_sig_subseteq.
  Qed.

  Global Instance : Inject Acceptor val := {| inject := inject ∘ proj1_sig |}.
  Global Instance : Inject Value val := {| inject := inject ∘ proj1_sig |}.

  Hint Extern 4 => unfold Acceptors' : core.

  Definition ballot_serialization := int_serialization.
  Definition acceptor_serialization :=
    sum_serialization
      ballot_serialization
      (prod_serialization ballot_serialization int_serialization).

  Definition proposer_serialization : serialization :=
    prod_serialization ballot_serialization
  (option_serialization (prod_serialization ballot_serialization int_serialization)).

  Definition learner_serialization :=
    prod_serialization ballot_serialization int_serialization.

  (** * Ghost resources *)
  Definition pending_class (i : nat) (b : Ballot) : iProp Σ :=
    own paxos_ballot_gname (pending_class i (size Proposers) b).
  Definition pending (b : Ballot) :=
    own paxos_ballot_gname (pending_ballot b).
  Definition shot (b : Ballot) (v : Value) :=
    own paxos_ballot_gname (shot_ballot b v).

  Definition msgs_auth (M : gset Message) : iProp Σ :=
    own paxos_messages_gname (● M) ∗ own paxos_messages_gname (◯ M).
  Definition msgs_elem_of (m : Message) : iProp Σ :=
    own paxos_messages_gname (◯ {[m]}).

  Definition maxBal_auth (f : Acceptor → option Ballot) : iProp Σ :=
    gen_heap_light_ctx paxos_maxBal_gname (fn_to_gmap Acceptors' f).
  Definition maxBal_frag (a : Acceptor) (b : option Ballot) :=
    lmapsto paxos_maxBal_gname a 1 b.

  Definition maxVal_auth (f : Acceptor → option (Ballot * Value)) : iProp Σ :=
    gen_heap_light_ctx paxos_maxVal_gname (fn_to_gmap Acceptors' f).
  Definition maxVal_frag (a : Acceptor) (mval : option (Ballot * Value)) :=
    lmapsto paxos_maxVal_gname a 1 mval.

  (** * Resource lemmas *)
  Lemma pending_pend_split i b :
    i < size Proposers →
    pending_class i b -∗ pending_class i (b + 1) ∗ pending (b * size Proposers + i).
  Proof.
    iIntros (?) "Hp".
    rewrite /pending_class pending_set_split //; last first.
    { apply Proposers_size_nonzero. }
    rewrite own_op //.
  Qed.

  Lemma pend_update_shot b v :
    pending b ==∗ shot b v.
  Proof. apply own_update, ballot_update. Qed.

  Lemma pending_shot b v :
    pending b -∗ shot b v -∗ False.
  Proof.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?%pending_shot_not_valid.
  Qed.

  Global Instance shot_persistent b v : Persistent (shot b v).
  Proof. apply _. Qed.

  Lemma shot_agree b v1 v2 : shot b v1 -∗ shot b v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[=]%shot_shot_valid.
    by simplify_eq.
  Qed.

  Lemma msgs_elem_of_in m M :
    msgs_auth M -∗ msgs_elem_of m -∗ ⌜m ∈ M⌝.
  Proof.
    iIntros "[HM _] Hm".
    iDestruct (own_op with "[$HM $Hm]") as "H".
    rewrite own_valid.
    iDestruct "H" as %[?%gset_included _]%auth_both_valid_discrete.
    iPureIntro. set_solver.
  Qed.

  Global Instance msgs_elem_of_persistent m : Persistent (msgs_elem_of m).
  Proof. rewrite /msgs_elem_of. apply _. Qed.

  Lemma msgs_update m M :
    msgs_auth M ==∗ msgs_auth (M ∪ {[m]}) ∗ msgs_elem_of m.
  Proof.
    iIntros "[HM HM']".
    iMod (own_update_2 _ _ _ (● (M ∪ {[m]}) ⋅ ◯ (M ∪ {[m]})) with "HM HM'")
      as "[HM HM']".
    { apply auth_update, gset_local_update. set_solver. }
    iAssert (own paxos_messages_gname (◯ (M ∪ {[m]})) ∗
             own paxos_messages_gname (◯ (M ∪ {[m]})))%I with "[HM']" as "[HM1 HM2]".
    { rewrite -own_op -auth_frag_op gset_op union_idemp_L //. }
    iFrame. iModIntro.
    iApply (own_mono with "HM1").
    apply auth_frag_mono, gset_included.
    set_solver.
  Qed.

  Lemma maxBal_valid f a b :
    maxBal_auth f -∗ maxBal_frag a b -∗ ⌜f a = b⌝.
  Proof.
    iIntros "HF hf".
    by iDestruct (gen_heap_light_valid with "HF hf") as %?%lookup_fn_to_gmap_1.
  Qed.

  Lemma maxBal_update b2 b1 f a :
    maxBal_auth f -∗ maxBal_frag a b1 ==∗
    maxBal_auth (<[a := b2]> f) ∗ maxBal_frag a b2.
  Proof.
    iIntros "HF hf".
    iMod (gen_heap_light_update with "HF hf") as "[HF Hf]".
    iFrame "Hf".
    rewrite /maxBal_auth fn_to_gmap_insert //. auto.
  Qed.

  Lemma maxVal_valid f a mv :
    maxVal_auth f -∗ maxVal_frag a mv -∗ ⌜f a = mv⌝.
  Proof.
    iIntros "HF hf".
    by iDestruct (gen_heap_light_valid with "HF hf") as %?%lookup_fn_to_gmap_1.
  Qed.

  Lemma maxVal_update mv1 mv2 f a :
    maxVal_auth f -∗ maxVal_frag a mv1 ==∗
    maxVal_auth (<[a := mv2]> f) ∗ maxVal_frag a mv2.
  Proof.
    iIntros "HF hf".
    iMod (gen_heap_light_update with "HF hf") as "[HF Hf]".
    iFrame "Hf".
    rewrite /maxVal_auth fn_to_gmap_insert //. auto.
  Qed.

  Lemma Acceptors_choose : ∃ a, a ∈ Acceptors.
  Proof.
    apply size_pos_elem_of, neq_0_lt, Nat.neq_sym.
    apply Acceptors_size_nonzero.
  Qed.

  Lemma Learners_nonempty : Learners ≢ ∅.
  Proof.
    intros ?%size_empty_iff.
    pose proof Learners_size_nonzero.
    lia.
  Qed.

  (** * Message serialization schemes *)
  Definition msg1a_ser (b : Ballot) := inl_ser_str (int_ser_str b).
  Definition mval_ser (mval : option (Ballot * Value)) :=
    match mval with
    | Some (mbal, mval) =>
      option_Some_ser_str
        (prod_ser_str (int_ser_str mbal) (int_ser_str (`mval)))
    | None => option_None_ser_str
    end.
  Definition msg1b_ser (b : Ballot) (mval : option (Ballot * Value)) :=
    prod_ser_str (int_ser_str b) (mval_ser mval).
  Definition msg2a_ser (b : Ballot) (val : Value) :=
    inr_ser_str (prod_ser_str (int_ser_str b) (int_ser_str (`val))).
  Definition msg2b_ser (b : Ballot) (val : Value) :=
    prod_ser_str (int_ser_str b) (int_ser_str (`val)).

  (* Predicate mapping messages in the model to physical messages *)
  Definition is_mdl_message (M : Message) (m : message) :=
    match M with
    | msg1a b =>
      ∃ (p : Proposer) (a : Acceptor), m = mkMessage (`p) (`a) (msg1a_ser b)
    | msg1b a b mv =>
      ∃ (p : Proposer), m = mkMessage (`a) (`p) (msg1b_ser b mv)
    | msg2a b v =>
      ∃ (p : Proposer) (a : Acceptor), m = mkMessage (`p) (`a) (msg2a_ser b v)
    | msg2b a b v =>
      ∃ (l : Learner), m = mkMessage (`a) (`l) (msg2b_ser b v)
  end.

  Definition messages_model_agree (δms : gset Message) (T : gset message) :=
    (∀ M, M ∈ δms → ∃ m, is_mdl_message M m ∧ m ∈ T) ∧
    (∀ m, m ∈ T → ∃ M, M ∈ δms ∧ is_mdl_message M m).

  (** * Socket interpretations *)
  Definition proposer_si : socket_interp Σ :=
    (λ m, ∃ (a : Acceptor) (b : Ballot) (mv : option (Ballot * Value)),
        (* phase 1b message *)
        ⌜s_is_ser proposer_serialization ($b, $mv) (m_body m)⌝ ∗
        ⌜m_sender m = `a⌝ ∗
        msgs_elem_of (msg1b a b mv))%I.

  Definition acceptor_si : socket_interp Σ :=
    (λ m, ∃ (p : Proposer),
        ⌜m_sender m = (`p)⌝ ∗
        (* either a phase1a message *)
        ((∃ (b : Ballot),
             ⌜s_is_ser acceptor_serialization (InjLV $b) (m_body m)⌝ ∗
             msgs_elem_of (msg1a b)) ∨
         (* or a phase2a message *)
         (∃ (b : Ballot) (v : Value),
             ⌜s_is_ser acceptor_serialization (InjRV ($b, $v)) (m_body m)⌝ ∗
             msgs_elem_of (msg2a b v))))%I.

  Definition learner_si : socket_interp Σ :=
    (λ m, ∃ (a : Acceptor) (b : Ballot) (val : Value),
        (* phase 2b message *)
        ⌜s_is_ser learner_serialization ($b, $val) (m_body m)⌝ ∗
        ⌜m_sender m = `a⌝ ∗
        shot b val ∗
        msgs_elem_of (msg2b a b val))%I.

  (** * Global invariant *)
  Definition messages_coh (δ : PaxosState) : iProp Σ :=
    ∃ (F : socket_address → message_soup) (Ts : message_soup),
      ([∗ set] a ∈ Acceptors, ∃ R, a @ acceptor_si ⤳# (R, F a)) ∗
      ([∗ set] p ∈ Proposers, ∃ R, p @ proposer_si ⤳# (R, F p)) ∗
      ⌜Ts = gset_flat_map F (Acceptors ∪ Proposers)⌝ ∗
      (* all messages in the model most correspond to a message sent by an
         Acceptor or a Proposer and vice versa. *)
      ⌜messages_model_agree δ.(msgs) Ts⌝.

  Definition ballot_inv (δ : PaxosState) : iProp Σ :=
    ∀ b v, ⌜msg2a b v ∈ δ.(msgs)⌝ -∗ shot b v.

  Definition paxos_inv : iProp Σ :=
    ∃ δ, frag_st δ ∗ msgs_auth δ.(msgs) ∗
         maxBal_auth δ.(maxBal) ∗ maxVal_auth δ.(maxVal) ∗
         messages_coh δ ∗ ballot_inv δ.
  Definition paxosN := nroot.@"paxos".

  Lemma paxos_inv_alloc E :
    frag_st PInit ∗
    ([∗ set] a ∈ Acceptors, a ⤳ (∅, ∅)) ∗
    ([∗ set] p ∈ Proposers, p ⤳ (∅, ∅)) ∗
    msgs_auth ∅ ∗
    maxBal_auth (λ _, None) ∗
    maxVal_auth (λ _, None)
    ⊢ |={E}=> inv paxosN paxos_inv.
  Proof.
    iIntros "(Hfrag & Hacceptors & Hproposers & HM & Hmb & Mv)".
    iApply inv_alloc.
    iModIntro. iExists _.
    iFrame. iFrame.
    iSplitL; [|by iIntros (???)].
    iExists (λ _, ∅), ∅.
    iSplitL "Hacceptors".
    { iApply (big_sepS_impl with "Hacceptors").
      iIntros "!#" (??) "Hsi". iExists _.
      by iApply (mapsto_messages_pers_alloc with "Hsi"). }
    iSplitL "Hproposers".
    { iApply (big_sepS_impl with "Hproposers").
      iIntros "!#" (??) "Hsi". iExists _.
        by iApply (mapsto_messages_pers_alloc with "Hsi"). }
    rewrite gset_flat_map_f_empty //.
  Qed.

  (** * Invariant lemmas *)
  Lemma ballot_inv_maxBal δ mb ms :
    ballot_inv (δ <| msgs ::= ms |>) -∗
    ballot_inv (δ <| maxBal ::= mb |> <| msgs ::= ms |>).
  Proof. done. Qed.

  Lemma ballot_inv_maxBal_maxVal δ mb mv ms  :
    ballot_inv (δ <| msgs ::= ms |>) -∗
    ballot_inv (δ <| maxBal ::= mb |> <| maxVal ::= mv |> <| msgs ::= ms |>).
  Proof. done. Qed.

  Lemma ballot_inv_send_not2a δ M :
    ¬ (∃ b v, M = msg2a b v) →
    ballot_inv δ -∗
    ballot_inv (δ <| msgs ::= λ ms, ms ∪ {[M]} |>).
  Proof.
    rewrite /ballot_inv /=.
    iIntros (Hm) "Hδ". iIntros (b v).
    rewrite elem_of_union ?elem_of_singleton.
    iDestruct 1 as "[% | %]"; [by iApply "Hδ"|].
    set_solver.
  Qed.

  Lemma ballot_inv_shot bal val δ :
    msgs_elem_of (msg2a bal val) -∗
    msgs_auth δ.(msgs) -∗
    ballot_inv δ -∗
    shot bal val ∗ msgs_auth δ.(msgs) ∗ ballot_inv δ.
  Proof.
    iIntros "Hm Hδ #HbI".
    iDestruct (msgs_elem_of_in with "Hδ Hm") as %?.
    iFrame "∗ #".
    by iApply "HbI".
  Qed.

  Lemma send_msg_notin x X m F φ :
    x ∉ X →
    ([∗ set] y ∈ X, ∃ R, y @ φ ⤳# (R, <[x:={[m]} ∪ F x]> F y))
    ⊣⊢ ([∗ set] y ∈ X, ∃ R, y @ φ ⤳# (R, F y)).
  Proof.
    iIntros (Hp).
    iApply big_sepS_proper.
    iIntros (a Ha) "/=".
    rewrite fn_lookup_insert_ne; eauto.
    set_solver.
  Qed.

  Lemma send_msg_combine x X m F  R φ :
    x ∈ X →
    x @ φ ⤳# (R, {[m]} ∪ F x) -∗
    ([∗ set] y ∈ (X ∖ {[x]}), ∃ R, y @ φ ⤳# (R, F y)) -∗
    [∗ set] y ∈ X, ∃ R, y @ φ ⤳# (R, <[x := {[m]} ∪ F x]> F y).
  Proof.
    iIntros (?) "Hp Hps".
    iDestruct (big_sepS_proper
                 (λ y, ∃ R0, y @ _ ⤳# (R0, (<[x :={[m]} ∪ F x]> F y)))%I
                 with "Hps") as "H".
    { iIntros (??). rewrite fn_lookup_insert_ne //. set_solver. }
    assert ({[m]} ∪ F x = <[x :={[m]} ∪ F x]> F x) as Heq.
    { rewrite fn_lookup_insert //. }
    rewrite {1}Heq.
    iDestruct (big_sepS_insert _ _ x with "[Hp $H]") as "Hps"; [set_solver|eauto|].
    rewrite -union_difference_singleton_L //.
  Qed.

  Lemma messages_agree_add (msgs : gset Message) F M m a (X : gset socket_address) :
    a ∈ X →
    is_mdl_message M m →
    messages_model_agree msgs (gset_flat_map F X) →
    messages_model_agree (msgs ∪ {[M]})
                         (gset_flat_map (<[a :={[m]} ∪ F a]> F) X).
  Proof.
    intros Ha HMm [HM HT]. split.
    - intros M' [HM' | ->%elem_of_singleton_1]%elem_of_union.
      + destruct (HM M' HM') as (?&?&?).
        eexists. split; [done|].
        by apply elem_of_gset_flat_map_fn_insert_2.
      + eexists. split; [done|].
        apply elem_of_gset_flat_map_fn_insert_1; [done|set_solver].
    - intros m' Hm'.
      apply gset_flat_map_insert_2_inv in Hm' as [-> | Hm']; [set_solver|].
      destruct (HT m' Hm') as (M' &?&?).
      exists M'. set_solver.
  Qed.

  Lemma messages_agree_duplicate (msgs : gset Message) F M m a
        (X : gset socket_address) :
    M ∈ msgs →
    is_mdl_message M m →
    messages_model_agree msgs (gset_flat_map F X) →
    messages_model_agree msgs (gset_flat_map (<[a:={[m]} ∪ F a]> F) X).
  Proof.
    intros Hin HM [Hm1 Hm2]. split.
    - intros M' HM'.
      destruct (Hm1 M' HM') as (m' & ? & ?).
      eexists. split; [done|].
      by apply elem_of_gset_flat_map_fn_insert_2.
    - intros m' [-> | ?]%gset_flat_map_insert_2_inv; eauto.
  Qed.

  Instance : Inj2 (=) (=) (=) msg2b_ser.
  Proof.
    rewrite /msg2b_ser /prod_ser_str /int_ser_str.
    intros ???? Hstr.
    destruct (decide (x1 = y1)) as [|Hneq]; simplify_eq; [done|].
    exfalso.
    apply char_splits_l in Hstr as [? Hstr].
    - simplify_eq.
      apply append_eq_length_inv in Hstr as [? ?]; [|done].
      simplify_eq.
    - intros ?. by apply get_StringOfZ_ne.
    - intros ?. apply get_n_append_ne; intros ?; by apply get_StringOfZ_ne.
  Qed.

   Lemma is_mdl_message_2b_inv M a l b v :
    is_mdl_message M (mkMessage (`a) l (msg2b_ser b v)) → M = msg2b a b v.
  Proof.
    destruct M.
    - destruct 1 as (?&?& [= Ha Hl Heq]).
      simplify_eq.
      pose proof ((proj2 (get_correct _ _) Heq 0)) as Hn.
      simpl in Hn.
      apply get_n_append_ne in Hn; [done| |].
      { intros ?. by eapply get_StringOfZ_ne. }
      intros ?. apply get_n_append_ne; [by intros []|].
      intros ?. apply get_n_append_ne; intros ?; by eapply get_StringOfZ_ne.
    - destruct 1 as (?& [= ? ? Heq]).
      simplify_eq.
      rewrite /msg2b_ser /msg1b_ser /prod_ser_str in Heq.
      symmetry in Heq.
      apply char_splits_l in Heq as [? Heq].
      + destruct (decide (String.length (StringOfZ b) = String.length (StringOfZ bal))).
        { simplify_eq.
          apply append_eq_length_inv in Heq as [? Hstr]; [|done].
          pose proof ((proj2 (get_correct _ _) Hstr 0)) as Hn.
          symmetry in Hn.
          destruct mval as [[]|]; by apply get_StringOfZ_ne in Hn. }
        pose proof ((proj2 (get_correct _ _) Heq (String.length (StringOfZ bal)))) as Hn.
        rewrite -(append_correct2 _ _ 0) in Hn.
        symmetry in Hn.
        destruct mval as [[]|].
        * apply get_n_append_ne in Hn; [done| |];
            intros ?; by eapply get_StringOfZ_ne.
        * apply get_n_append_ne in Hn; [done| |];
            intros ?; by eapply get_StringOfZ_ne.
      + intros ?. by apply get_StringOfZ_ne.
      + intros ?. apply get_n_append_ne; intros ?; by apply get_StringOfZ_ne.
    - destruct 1 as (?&?& [= ? ? Heq]).
      pose proof ((proj2 (get_correct _ _) Heq 0)) as Hn.
      simpl in Hn.
      apply get_n_append_ne in Hn; [done| |].
      { intros ?. by eapply get_StringOfZ_ne. }
      intros ?. apply get_n_append_ne; [by intros []|].
      intros ?. apply get_n_append_ne; intros ?; by eapply get_StringOfZ_ne.
    - destruct 1 as (?& [= ? ? Heq]). by simplify_eq.
  Qed.

End paxos_prelude.

#[global] Hint Extern 1 (_ ∉ _) => apply proposer_not_acceptor : core.
#[global] Hint Extern 1 (_ ∉ _) => apply acceptor_not_proposer : core.

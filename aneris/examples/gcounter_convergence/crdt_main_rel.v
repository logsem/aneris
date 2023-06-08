From stdpp Require Import finite vector.
From trillium.prelude Require Import finitary classical quantifiers.
From trillium.program_logic Require Import traces.
From aneris.prelude Require Import misc.
From aneris.prelude Require Import time.
From aneris.aneris_lang Require Import state_interp adequacy.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.examples.gcounter_convergence Require Import
     crdt_model crdt_resources crdt_runner vc.
From trillium.traces Require Import trace_properties.

Import InfListNotations.

Local Instance: ∀ gcdata st st', ProofIrrel (GCounterM gcdata st st').
Proof. intros ?????; apply ProofIrrelevance. Qed.

Lemma GcounterM_rel_finitary gcdata : aneris_model_rel_finitary (GCounterM gcdata).
Proof.
  intros st.
  apply finite_smaller_card_nat.
  apply (@in_list_finite
            _ _ (λ st', GCounterM gcdata st st') _
            (all_crdt_states_smaller (GClen gcdata) (vmap S (max_vc st)))).
  intros ? ?.
  apply elem_of_all_crdt_states_smaller.
  intros ?.
  apply crdt_next_bounded; done.
Qed.

Definition oloc_less_defined (ol ol' : option loc) : Prop :=
  match ol with
  | Some l =>
    match ol' with
    | Some l' => l' = l
    | None => False
    end
  | None => True
  end.

Global Instance oloc_less_defined_PO : PartialOrder oloc_less_defined.
Proof.
  constructor; first constructor.
  - intros []; split; auto.
  - intros [] [] [] [] []; split; intros; simplify_eq/=; eauto.
  - intros [] [] [] []; auto.
Qed.

Definition locs_less_defined (locs locs' : list (option loc)) : Prop :=
  Forall2 oloc_less_defined locs locs'.

Lemma locs_less_defined_lookup locs locs' i :
  locs_less_defined locs locs' → oloc_less_defined (locs !!! i) (locs' !!! i).
Proof.
  rewrite /locs_less_defined Forall2_lookup.
  intros Hlocs.
  specialize (Hlocs i).
  rewrite !list_lookup_total_alt.
  destruct (locs !! i); destruct (locs' !! i); inversion Hlocs; simplify_eq; done.
Qed.

Global Instance locs_less_defined_PO : PartialOrder locs_less_defined.
Proof.
  constructor; first constructor.
  - intros l; apply (_ : Reflexive (Forall2 _)).
  - intros l1 l2 l3; apply (_ : Transitive (Forall2 _)).
  - intros l1 l2; apply (_ : AntiSymm _ (Forall2 _)).
Qed.

Lemma locs_all_defined locs locs' :
  locs_less_defined (Some <$> locs) locs' → locs' = (Some <$> locs).
  intros Hld.
  apply list_eq; intros i.
  destruct (decide (i < length locs)) as [Hlt|Hnlt].
  - destruct (lookup_lt_is_Some_2 locs i) as [l Hl]; first done.
    destruct (lookup_lt_is_Some_2 locs' i) as [ol Hol].
    { erewrite <- (Forall2_length); last apply Hld.
      rewrite fmap_length; done. }
    apply (locs_less_defined_lookup _ _ i) in Hld.
    revert Hld.
    rewrite list_lookup_fmap list_lookup_total_fmap //.
    erewrite !list_lookup_total_correct; eauto.
    intros Hld.
    rewrite Hl Hol; simpl.
    destruct ol; simplify_eq/=; done.
  - rewrite list_lookup_fmap (lookup_ge_None_2 locs); last lia.
    rewrite lookup_ge_None_2; first done.
    erewrite <- (Forall2_length); last apply Hld.
    rewrite fmap_length; lia.
Qed.

Section crdt_main_rel.
  Context (gcdata : GCData).

  Implicit Types ex : execution_trace aneris_lang.
  Implicit Types iex : inf_execution_trace aneris_lang.
  Implicit Types atr : finite_trace (GCounterM gcdata) ().
  Implicit Types iatr : inflist (() * GCounterM gcdata).

  Notation ith_sa i := (gcd_addr_list gcdata !!! i).

  Definition loc_of_trace_i (i : nat) (evs : event_obs aneris_lang) : option loc :=
    match evs with
    | [] => None
    | ev :: evs' =>
      match expr_e ev.(post_expr) with
      | Val #(LitLoc l) => Some l
      | _ => None
      end
    end.

  Definition locs_of_trace_now (ex : execution_trace aneris_lang) : list (option loc) :=
    (λ i, loc_of_trace_i i (events_of_trace (allocEV (StringOfZ i)) ex) ) <$> seq 0 (GClen gcdata).

  Fixpoint locs_of_trace (ex : execution_trace aneris_lang) : finite_trace (list (option loc)) () :=
    match ex with
    | trace_singleton _ => {tr[replicate (GClen gcdata) None]}
    | trace_extend ex' _ c => (locs_of_trace ex') :tr[()]: (locs_of_trace_now ex)
    end.

  Lemma locs_of_trace_last ex :
    trace_last (locs_of_trace ex) = locs_of_trace_now ex.
  Proof.
    destruct ex; last done.
    rewrite /locs_of_trace_now.
    rewrite (const_fmap _ _ None); first by rewrite seq_length.
    intros ?; rewrite events_of_singleton_trace; done.
  Qed.

  Lemma locs_of_trace_now_length ex : length (locs_of_trace_now ex) = GClen gcdata.
  Proof. rewrite /locs_of_trace fmap_length seq_length; done. Qed.

  Lemma locs_of_trace_length ex : trace_forall (λ tr, length tr = GClen gcdata) (locs_of_trace ex).
  Proof.
    induction ex as [|ex IHex c]; simpl in *.
    - constructor. rewrite replicate_length //.
    - constructor; first done. apply locs_of_trace_now_length.
  Qed.

  Lemma locs_of_trace_now_extend_less_defined ex c oζ:
    valid_exec (ex :tr[oζ]: c) →
    locs_less_defined (locs_of_trace_now ex) (locs_of_trace_now (ex :tr[oζ]: c)).
  Proof.
    intros Hvl.
    apply Forall2_lookup; intros i.
    destruct (decide (i < GClen gcdata)); last first.
    { rewrite !lookup_ge_None_2; first by constructor.
      - rewrite locs_of_trace_now_length; lia.
      - rewrite locs_of_trace_now_length; lia. }
    rewrite !list_lookup_fmap !lookup_seq_lt //=; [].
    constructor.
    destruct (events_of_trace_extend_app (allocEV (StringOfZ i)) ex c oζ) as (evs & _ & Heq & _);
      first done.
    rewrite Heq.
    destruct (events_of_trace (allocEV (StringOfZ i)) ex); reflexivity.
  Qed.

  Lemma locs_of_trace_less_defined ex :
    valid_exec ex → trace_steps (λ x _ y, locs_less_defined x y) (locs_of_trace ex).
  Proof.
    induction ex as [|ex IHex c]; simpl; first by constructor.
    intros Hvl.
    econstructor; [done| |by apply IHex; eapply valid_exec_exec_extend_inv; eauto].
    rewrite locs_of_trace_last.
    apply locs_of_trace_now_extend_less_defined; done.
  Qed.

  Lemma locs_of_trace_now_lookup_singleton i ex ip lbl l v σ h :
    i < GClen gcdata →
    events_of_trace (allocEV (StringOfZ i)) ex = [allocObs ip lbl l v σ h] →
    locs_of_trace_now ex !! i = Some (Some l).
  Proof.
    intros Hi Hevs.
    rewrite /locs_of_trace list_lookup_fmap lookup_seq_lt /=; last done.
    rewrite /loc_of_trace_i Hevs; done.
  Qed.

  Lemma locs_of_trace_now_lookup_nil i ex :
    i < GClen gcdata →
    events_of_trace (allocEV (StringOfZ i)) ex = [] →
    locs_of_trace_now ex !! i = Some None.
  Proof.
    intros Hi Hevs.
    rewrite /locs_of_trace list_lookup_fmap lookup_seq_lt /=; last done.
    rewrite /loc_of_trace_i Hevs; done.
  Qed.

  Definition valid_model_fin_trace (mtr : finite_trace (GCounterM gcdata) ()) : Prop :=
    trace_forall valid_crdt_state mtr ∧ trace_steps (λ st _ st', st = st' ∨ CrdtNext st tt st') mtr.

  Definition gcounter_values_related_now (lcs : (list (option loc)))
             (c : cfg aneris_lang) (δ : GCounterM gcdata) : Prop :=
    ∀ i : fin (GClen gcdata),
       match lcs !!! (fin_to_nat i) with
       | Some l =>
         ∃ h, c.2.(state_heaps) !! (ip_of_address (ith_sa (fin_to_nat i))) = Some h ∧
              h !! l = Some (vector_clock_to_val (vec_to_list (δ !!! i)))
       | None => δ !!! i = vreplicate (GClen gcdata) 0
       end.

  Definition gcounter_values_related (locs : finite_trace (list (option loc)) ())
             (ex : execution_trace aneris_lang) (mtr : finite_trace (GCounterM gcdata) ()) : Prop :=
    trace_forall3 gcounter_values_related_now locs ex mtr.

  Definition gcounter_values_related_now_locs_resolved (lcs : (list loc))
             (c : cfg aneris_lang) (δ : GCounterM gcdata) : Prop :=
    ∀ i : fin (GClen gcdata),
      ∃ h, c.2.(state_heaps) !! (ip_of_address (ith_sa (fin_to_nat i))) = Some h ∧
           h !! (lcs !!! (fin_to_nat i)) = Some (vector_clock_to_val (vec_to_list (δ !!! i))).

  Lemma gcounter_values_related_now_resolve_locs locs c δ :
    length locs = GClen gcdata →
    gcounter_values_related_now (Some <$> locs) c δ →
    gcounter_values_related_now_locs_resolved locs c δ.
  Proof.
    intros Hlen Hvrel i.
    specialize (Hvrel i).
    rewrite list_lookup_total_fmap in Hvrel; [done|by rewrite Hlen; apply fin_to_nat_lt].
  Qed.

  Definition gcounter_monotone (locs : finite_trace (list (option loc)) ())
             (ex : execution_trace aneris_lang) : Prop :=
    trace_steps2
       (λ lcs c _ _ lcs' c',
          ∀ i, i < GClen gcdata →
               match lcs !!! i with
               | Some l =>
                 match lcs' !!! i with
                 | Some l' =>
                   l' = l ∧
                   ∃ h h' (vc vc' : vector_clock (GClen gcdata)),
                      c.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h ∧
                      c'.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h' ∧
                      h !! l = Some (vector_clock_to_val vc) ∧
                      h' !! l = Some (vector_clock_to_val vc') ∧
                      vc_le vc vc'
                 | None => False
                 end
               | None => True
               end) locs ex.

  Definition gcounter_monotone_configs (lcs : list loc) (c c' : cfg aneris_lang) : Prop :=
    c = c' ∨
    ∀ i, i < GClen gcdata →
         ∃ h h' (vc vc' : vector_clock (GClen gcdata)),
            c.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h ∧
            c'.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h' ∧
            h !! (lcs !!! i) = Some (vector_clock_to_val vc) ∧
                 h' !! (lcs !!! i) = Some (vector_clock_to_val vc') ∧
                 vc_le vc vc'.

  Lemma gcounter_monotone_configs_vc_le lcs i c c' h h' (vc vc' : vector_clock (GClen gcdata)) :
    i < GClen gcdata →
    gcounter_monotone_configs lcs c c' →
    c.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h →
    c'.2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h' →
    h !! (lcs !!! i) = Some (vector_clock_to_val (vec_to_list vc)) →
    h' !! (lcs !!! i) = Some (vector_clock_to_val (vec_to_list vc')) →
    vc_le vc vc'.
  Proof.
    intros Hi Hgmc Hh Hh' Hvc Hvc'.
    destruct Hgmc as [<-|Hgmc].
    { simplify_eq.
      match goal with
      | Heq :  _ =  _ |- _ =>
        apply vec_to_list_inj2 in Heq; simplify_eq; done
      end. }
    specialize (Hgmc i Hi) as (?&?&?&?&?&?&?&?&?); simplify_eq.
    repeat
       match goal with
       | Heq :  _ =  _ |- _ =>
         apply vec_to_list_inj2 in Heq; simplify_eq
       end; done.
  Qed.

  Global Instance gcounter_monotone_configs_PreOrder lcs : PreOrder (gcounter_monotone_configs lcs).
  Proof.
    split.
    - by left.
    - intros c1 c2 c3 Hc12 Hc23.
      destruct Hc12 as [->|Hc12]; first done.
      destruct Hc23 as [<-|Hc23]; first by right.
      right.
      intros i Hi.
      destruct (Hc12 i Hi) as (h1&h2&vc1&vc2&?&?&?&?&?).
      destruct (Hc23 i Hi) as (h2'&h3&vc2'&vc3&?&?&?&?&?).
      simplify_eq/=.
      match goal with
       | Heq : _ =  _ |- _ =>
         apply vec_to_list_inj2 in Heq; simplify_eq
      end.
      eexists h1, h3, vc1, vc3; split_and!; [by eauto|by eauto|done|done|etrans; eauto].
  Qed.

  Definition gcounter_monotone_locs_resolved_simple
             (lcs : list loc) (l : list (cfg aneris_lang)) : Prop :=
    ∀ i c1 c2, l !! i = Some c1 → l !! (S i) = Some c2 → gcounter_monotone_configs lcs c1 c2.

  Definition gcounter_monotone_locs_resolved (lcs : list loc) (l : list (cfg aneris_lang)) : Prop :=
    ∀ i j c1 c2, i ≤ j → l !! i = Some c1 → l !! j = Some c2 → gcounter_monotone_configs lcs c1 c2.

  Lemma gcounter_monotone_locs_resolved_if_simple lcs l :
    gcounter_monotone_locs_resolved_simple lcs l → gcounter_monotone_locs_resolved lcs l.
  Proof.
    intros Hgms i j c1 c2 Hij Hi Hj.
    apply Nat.le_sum in Hij as [k Hk].
    revert i j Hk c1 c2 Hi Hj.
    induction k as [|k IHk]; intros i j Hk c1 c2 Hi Hj.
    { assert (j = i) by lia; clear Hk; simplify_eq; reflexivity. }
    destruct (lookup_lt_is_Some_2 l (i + k)) as [c Hc].
    { apply lookup_lt_Some in Hj; lia. }
    etrans; first by apply (IHk i (i + k) eq_refl c1 c); auto.
    replace j with (S (i + k)) in Hj by lia.
    eapply Hgms; eauto.
  Qed.

  Lemma gcounter_monotone_resolve_locs lcs ex il l :
    length il = length l →
    length lcs = GClen gcdata →
    valid_exec (ex +trl+ l) →
    trace_last (locs_of_trace ex) = (Some <$> lcs) →
    trace_steps (λ x _ y, locs_less_defined x y) (locs_of_trace ex +trl+ il) →
    gcounter_monotone (locs_of_trace ex +trl+ il) (ex +trl+ l) →
    gcounter_monotone_locs_resolved lcs (trace_last ex :: map snd l).
  Proof.
    intros Hlen Hlcs Hvl Hld Hldl Hgms.
    apply gcounter_monotone_locs_resolved_if_simple.
    revert il Hlen Hvl Hld Hldl Hgms; induction l as [|[oζ c] l IHl] using rev_ind;
      intros il Hlen Hvl Hld Hldl Hgms.
    { intros i j c1 c2; rewrite list_lookup_singleton; done. }
    intros i c1 c2 Hi HSi.
    destruct il as [|[[] locs] il _] using rev_ind.
    { rewrite app_length /= in Hlen; lia. }
    rewrite -!trace_append_list_assoc /= in Hvl, Hgms, Hldl.
    assert (i < S (length l)).
    { cut (S i < length (trace_last ex :: map snd l ++ [c])).
      - rewrite /= app_length map_length /=; lia.
      - apply lookup_lt_is_Some_1; eauto.
        rewrite map_app in HSi. rewrite HSi; eauto. }
    rewrite map_app (lookup_app_l (_ :: _)) in Hi; last first.
    { list_simplifier. rewrite map_length //. }
    destruct (decide (i < length l)) as [Hlt|Hnlt].
    - rewrite /= map_app lookup_app_l in HSi; last by rewrite map_length.
      eapply (IHl il); [rewrite !app_length /= in Hlen| |done| | |by eauto|by eauto].
      + rewrite !Nat.add_1_r in Hlen. by injection Hlen.
      + eapply valid_exec_exec_extend_inv; eauto.
      + eapply trace_steps_step_inv in Hldl as [? ?]; done.
      + eapply trace_steps2_step_inv in Hgms as [? ?]; done.
    - assert (i = length l) as HSieq by lia.
      rewrite HSieq in HSi.
      rewrite map_app (lookup_app_r (_ :: _)) in HSi; last by rewrite /= map_length.
      rewrite /= map_length Nat.sub_diag in HSi; simplify_eq/=.
      apply trace_steps2_step_inv in Hgms as [_ Hgms].
      destruct Hgms as (? & ? & ?%last_eq_trace_ends_in & ?%last_eq_trace_ends_in & Hgms).
      simplify_eq.
      destruct l as [|[? c'] l _] using rev_ind.
      + assert (length il = 0) by by rewrite app_length /= in Hlen; lia.
        destruct il; last done.
        simplify_eq/=.
        rewrite Hld in Hgms.
        right; intros i Hi.
        specialize (Hgms i Hi).
        rewrite list_lookup_total_fmap in Hgms; last lia.
        destruct (locs !!! i); last done.
        destruct Hgms as [-> Hgms]; done.
      + rewrite -!trace_append_list_assoc /= in Hgms.
        rewrite app_length /= in Hi.
        rewrite map_app (lookup_app_r (_ ::_)) in Hi; last by rewrite /= map_length; lia.
        rewrite /= in Hi.
        replace (length l + 1 - S (length l)) with 0 in Hi by lia.
        simplify_eq/=.
        apply valid_exec_exec_extend_inv in Hvl as [Hvl _].
        apply locs_of_trace_less_defined in Hvl.
        apply trace_steps_step_inv in Hldl as [Hldl _].
        eapply trace_append_list_steps_rtc_nl in Hldl;
          [|apply trace_ends_in_last|apply trace_ends_in_last].
        revert Hldl; rewrite rt_rtc_same Hld; intros Hldl.
        right. intros i Hilen.
        apply (locs_less_defined_lookup _ _ i) in Hldl.
        rewrite list_lookup_total_fmap in Hldl; last lia.
        specialize (Hgms i Hilen).
        destruct (trace_last (locs_of_trace ex +trl+ il) !!! i) as [ol'|]; last done.
        simplify_eq/=.
        destruct (locs !!! i); last done.
        destruct Hgms as (-> & Hgms).
        by list_simplifier.
  Qed.

  Definition send_evs_rel (locs : list (option loc)) (ex : execution_trace aneris_lang) : Prop :=
    ∃ sevss,
       length sevss = GClen gcdata ∧
       ∀ i, i < GClen gcdata →
            ∃ sevs,
               sevss !! i = Some sevs ∧
               sendevs_valid sevs ∧
               match locs !!! i with
               | Some l =>
                 Forall2
                    (@send_events_correspond gcdata (ith_sa i) l)
                    (events_of_trace (sendonEV (ith_sa i)) ex)
                    sevs
               | None => events_of_trace (sendonEV (ith_sa i)) ex = [] ∧ sevs = []
               end.

  Definition send_evs_rel_locs_resolved
             (locs : list loc) (ex : execution_trace aneris_lang) : Prop :=
    ∃ sevss,
       length sevss = GClen gcdata ∧
       ∀ i, i < GClen gcdata →
            ∃ sevs,
               sevss !! i = Some sevs ∧
               sendevs_valid sevs ∧
               Forall2
                  (@send_events_correspond gcdata (ith_sa i) (locs !!! i))
                  (events_of_trace (sendonEV (ith_sa i)) ex)
                  sevs.

  Lemma send_evs_rel_resolve_locs locs ex :
    length locs = GClen gcdata →
    send_evs_rel (Some <$> locs) ex →
    send_evs_rel_locs_resolved locs ex.
  Proof.
    intros Hlen [sevss [? Hsevs]].
    exists sevss; split; first done.
    intros i Hi.
    specialize (Hsevs i Hi).
    setoid_rewrite list_lookup_total_fmap in Hsevs; [eauto|lia].
  Qed.


  Definition receive_evs_rel (locs : list (option loc)) (ex : execution_trace aneris_lang) : Prop :=
    ∃ revss,
       length revss = GClen gcdata ∧
       ∀ i, i < GClen gcdata →
            ∃ revs,
               revss !! i = Some revs ∧
               match locs !!! i with
               | Some l =>
                 Forall2 (rec_events_correspond (ith_sa i))
                         (events_of_trace (receiveonEV (ith_sa i)) ex) revs ∧
                 ∃ h (vc : vector_clock (GClen gcdata)),
                    (trace_last ex).2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h ∧
                    h !! l = Some (vector_clock_to_val vc) ∧
                 forall j rev, S j < length revs → revs !! j = Some rev → vc_le rev vc
               | None => events_of_trace (receiveonEV (ith_sa i)) ex = [] ∧ revs = []
               end.

  Definition receive_evs_rel_locs_resolved
             (locs : list loc) (ex : execution_trace aneris_lang) : Prop :=
    ∃ revss,
       length revss = GClen gcdata ∧
       ∀ i, i < GClen gcdata →
            ∃ revs,
               revss !! i = Some revs ∧
               Forall2 (rec_events_correspond (ith_sa i))
                         (events_of_trace (receiveonEV (ith_sa i)) ex) revs ∧
               ∃ h (vc : vector_clock (GClen gcdata)),
                  (trace_last ex).2.(state_heaps) !! (ip_of_address (ith_sa i)) = Some h ∧
                  h !! (locs !!! i) = Some (vector_clock_to_val vc) ∧
                  forall j rev, S j < length revs → revs !! j = Some rev → vc_le rev vc.

  Lemma receive_evs_rel_resolve_locs locs ex :
    length locs = GClen gcdata →
    receive_evs_rel (Some <$> locs) ex →
    receive_evs_rel_locs_resolved locs ex.
  Proof.
    intros Hlen [revss [? Hrevs]].
    exists revss; split; first done.
    intros i Hi.
    specialize (Hrevs i Hi).
    setoid_rewrite list_lookup_total_fmap in Hrevs; [eauto|lia].
  Qed.

  Definition crdt_main_rel (ex: execution_trace aneris_lang)
             (mtr : auxiliary_trace (aneris_to_trace_model (GCounterM gcdata))) : Prop :=
    valid_system_trace ex mtr ∧
    valid_model_fin_trace mtr ∧
    gcounter_values_related (locs_of_trace ex) ex mtr ∧
    send_evs_rel (trace_last (locs_of_trace ex)) ex ∧
    receive_evs_rel (trace_last (locs_of_trace ex)) ex.

  Lemma crdt_main_rel_monotone ex mtr :
    crdt_main_rel ex mtr → gcounter_monotone (locs_of_trace ex) ex.
  Proof.
    intros (Hvl & Hmvl & Hvrel & _).
    revert mtr Hvl Hmvl Hvrel.
    induction ex as [|ex IHex c]; simpl;
      intros mtr Hvl Hmvl Hvrel; first by apply trace_steps2_singleton.
    econstructor; [done|done| |]; last first.
    { apply trace_forall3_extend_inv_l in Hvrel as (? & ? & ? & mtr' & ? & [] & ? & ? & ? & ?); simplify_eq.
      inversion Hvl; simplify_eq.
      eapply IHex.
      - done.
      - destruct Hmvl as [[? ?]%trace_forall_extend_inv [? [??]]%trace_steps_step_inv]; done.
      - by eauto. }
    apply trace_forall3_extend_inv_l in Hvrel as (c' & ex' & st & mtr' & oζ & ? & ? & ? & Hrel1 & Hrel2);
      simplify_eq/=.
    apply trace_forall3_last in Hrel1.
    intros i Hi.
    specialize (Hrel1 (nat_to_fin Hi)).
    specialize (Hrel2 (nat_to_fin Hi)).
    rewrite locs_of_trace_last in Hrel1.
    rewrite locs_of_trace_last.
    rewrite !fin_to_nat_to_fin in Hrel1, Hrel2.
    eapply valid_system_trace_valid_exec_trace in Hvl.
    destruct (locs_of_trace_now (ex' :tr[ oζ ]: c') !!! i) eqn:Heq; last first.
    { pose proof (locs_of_trace_now_extend_less_defined ex' c' _ Hvl) as Hld.
      apply (locs_less_defined_lookup _ _ i) in Hld.
      rewrite Heq in Hld.
      destruct (locs_of_trace_now ex' !!! i); done. }
    pose proof (locs_of_trace_now_extend_less_defined ex' c' _ Hvl) as Hld.
    apply (locs_less_defined_lookup _ _ i) in Hld.
    rewrite Heq in Hld.
    destruct (locs_of_trace_now ex' !!! i); simplify_eq/=; last done.
    split; first done.
    destruct Hrel1 as (h & Hh1 & Hh2).
    destruct Hrel2 as (h' & Hh'1 & Hh'2).
    eexists _, _, _, _; split_and!; [by eauto|by eauto|by eauto|by eauto|].
    destruct Hmvl as [_ Hmvl].
    apply trace_steps_step_inv in Hmvl as [_ (st' & -> & [->|Hmvl])]; first done.
    apply crdt_next_vc_le; done.
  Qed.

  Lemma crdt_main_rel_initially (ps : programs_using_gcounters gcdata) v :
    crdt_main_rel
       {tr[ ([{| expr_n := "system"; expr_e := runner gcdata 0 (progs ps) v |}],
             init_state) ]}
       {tr[ initial_crdt_state (GClen gcdata) ]}.
  Proof.
    rewrite /crdt_main_rel /=; split_and!.
    - constructor.
    - repeat constructor. apply valid_initial_crdt_state.
    - constructor; intros i.
      rewrite lookup_total_replicate_2; last by apply fin_to_nat_lt.
      rewrite vlookup_replicate; done.
    - exists (replicate (length (gcd_addr_list gcdata)) []).
      split; first by rewrite replicate_length.
      intros i Hi.
      exists []; split; first by rewrite lookup_replicate_2.
      split.
      { intros ????; rewrite lookup_nil; done. }
      rewrite lookup_total_replicate_2; last done.
      rewrite events_of_singleton_trace; done.
    - exists (replicate (length (gcd_addr_list gcdata)) []).
      split; first by rewrite replicate_length.
      intros i Hi.
      exists []; split; first by rewrite lookup_replicate_2.
      rewrite lookup_total_replicate_2; last done.
      rewrite events_of_singleton_trace; done.
  Qed.

  Lemma crdt_main_rel_step (ps : programs_using_gcounters gcdata) v ex
        (atr atr': auxiliary_trace (aneris_to_trace_model (GCounterM gcdata))) ex' oζ ℓ:
    valid_system_trace ex atr →
    trace_contract ex oζ ex' →
    trace_contract atr ℓ atr' →
    crdt_main_rel ex' atr' →
    trace_starts_in ex
      ([{| expr_n := "system"; expr_e := runner gcdata 0 (progs ps) v |}], init_state) →
    trace_starts_in atr (initial_crdt_state (GClen gcdata)) →
    valid_state_evolution (ex' :tr[oζ]: trace_last ex) (atr' :tr[ℓ]: trace_last atr) →
    (∀ i : fin (length (gcd_addr_list gcdata)),
      match locs_of_trace_now ex !!! (fin_to_nat i) with
      | Some l =>
        ∃ h : heap,
          (trace_last ex).2.(state_heaps) !! ip_of_address (ith_sa (fin_to_nat i)) = Some h ∧
          h !! l = Some (vector_clock_to_val (vec_to_list ((trace_last atr) !!! i)))
      | None => (trace_last atr) !!! i = vreplicate (length (gcd_addr_list gcdata)) 0
     end) →
    send_evs_rel (locs_of_trace_now ex) ex →
    receive_evs_rel (locs_of_trace_now ex) ex →
    crdt_main_rel ex atr.
  Proof.
    intros Hvls [c ->] [δ ->] Hmrel Hex's Hatr's Hvse Hstrel Hsevsrel Hrevsrel; simpl in *.
    rewrite /crdt_main_rel /=; split_and!.
    - done.
    - split.
      + constructor; first by apply Hmrel.
        destruct Hmrel as (_ & [Hvst _] & _).
        apply trace_forall_last in Hvst.
        destruct Hvse as [<-|]; first done.
        eapply CrdtNext_preserves_validity; done.
      + destruct Hmrel as (_ & [_ Hststep] & _).
        econstructor; [done | | done].
        destruct Hvse as [<-|]; by auto.
    - constructor; [by apply Hmrel|done].
    - done.
    - done.
  Qed.

  CoFixpoint locs_of_inf_trace
             (ex : execution_trace aneris_lang)
             (iex: inf_execution_trace aneris_lang) : inflist (() * list (option loc)) :=
    match iex with
    | []%inflist => []
    | ((oζ, c) :: iex')%inflist =>
      (tt, (locs_of_trace_now (ex :tr[oζ]: c))) :: locs_of_inf_trace (ex :tr[oζ]: c) iex'
    end.

  Lemma locs_of_inf_trace_take ex iex n :
    ((locs_of_trace ex) +trl+ (inflist_take n (locs_of_inf_trace ex iex))) =
    locs_of_trace (ex +trl+ (inflist_take n iex)).
  Proof.
    revert ex iex; induction n as [|n IHn]; intros ex iex; simpl; first done.
    destruct iex as [|[??]?]; simpl; first done.
    rewrite -IHn; done.
  Qed.

  Lemma locs_of_inf_trace_length ex iex : inflist_same_length (locs_of_inf_trace ex iex) iex.
  Proof.
    intros n.
    revert ex iex.
    induction n; simpl; intros ex iex.
    - rewrite (inflist_unfold_fold (locs_of_inf_trace ex iex)).
      destruct iex as [|[??]?]; simpl; done.
    - destruct iex as [|[??]?]; done.
  Qed.

  Lemma locs_of_inf_trace_cons_inv ex iex lcs ilocs:
    locs_of_inf_trace ex iex = (lcs :: ilocs)%inflist →
    ∃ oζ c iex',
       iex = ((oζ, c):: iex')%inflist ∧
       lcs = (tt, locs_of_trace_now (ex :tr[oζ]: c)) ∧
       ilocs = locs_of_inf_trace (ex :tr[oζ]: c) iex'.
  Proof.
    rewrite (inflist_unfold_fold (locs_of_inf_trace ex iex)).
    destruct iex as [|[??]?]; simpl; first done.
    intros; simplify_eq; eauto 10.
  Qed.

  Lemma locs_of_inf_trace_less_defined ex iex :
    valid_inf_exec ex iex →
    always
       (λ locs ilocs, trace_steps (λ x _ y, locs_less_defined x y) locs)
       (locs_of_trace ex) (locs_of_inf_trace ex iex).
  Proof.
    intros Hvex.
    apply always_take_drop; intros n.
    rewrite locs_of_inf_trace_take.
    apply locs_of_trace_less_defined.
    eapply valid_inf_exe_valid_exec.
    apply valid_inf_exe_take_drop; done.
  Qed.

  Definition crdt_main_rel_ternary
             (locs : finite_trace (list (option loc)) ()) (ex: execution_trace aneris_lang)
             (mtr : auxiliary_trace (aneris_to_trace_model (GCounterM gcdata)))
             (ilocs : inflist (() * list (option loc))) (iex: inf_execution_trace aneris_lang)
             (imtr : inflist (() * GCounterM gcdata)) : Prop :=
    valid_system_trace ex mtr ∧
    valid_model_fin_trace mtr ∧
    gcounter_values_related locs ex mtr ∧
    send_evs_rel (trace_last locs) ex ∧
    receive_evs_rel (trace_last locs) ex.

  Lemma crdt_main_rel_ternary_crdt_main_rel ex mtr ilocs iex imtr :
    crdt_main_rel_ternary (locs_of_trace ex) ex mtr ilocs iex imtr → crdt_main_rel ex mtr.
  Proof. intros (?&?&?&?&?); split_and!; done. Qed.

  (* move *)
  Lemma valid_inf_system_trace_take_drop n
        {Λ : language} {M} (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (iex : inf_execution_trace Λ) (iatr : inf_auxiliary_trace M) :
    valid_inf_system_trace φ ex atr iex iatr →
    valid_inf_system_trace φ
      (ex +trl+ inflist_take n iex) (atr +trl+ inflist_take n iatr)
      (inflist_drop n iex) (inflist_drop n iatr).
  Proof.
    revert ex atr iex iatr.
    induction n as [|n IHn]; first done.
    intros ex atr iex iatr Hvisf.
    inversion Hvisf; simplify_eq/=; first done.
    apply IHn; done.
  Qed.
  Lemma valid_inf_system_trace_length
        {Λ : language} {M} (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (iex : inf_execution_trace Λ) (iatr : inf_auxiliary_trace M) :
    valid_inf_system_trace φ ex atr iex iatr → inflist_same_length iex iatr.
  Proof.
    intros Hvisf n.
    apply (valid_inf_system_trace_take_drop n) in Hvisf.
    inversion Hvisf; simplify_eq/=; done.
  Qed.
  Lemma valid_inf_system_trace_mono
        {Λ : language} {M} (φ ψ : execution_trace Λ → auxiliary_trace M → Prop)
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (iex : inf_execution_trace Λ) (iatr : inf_auxiliary_trace M) :
    (∀ (ex' : execution_trace Λ) (atr' : auxiliary_trace M), φ ex' atr' → ψ ex' atr') →
    valid_inf_system_trace φ ex atr iex iatr → valid_inf_system_trace ψ ex atr iex iatr.
  Proof.
    revert ex atr iex iatr; cofix IH; intros ex atr iex iatr Hφψ Hφ.
    inversion Hφ; simplify_eq.
    - constructor; apply Hφψ; done.
    - econstructor; eauto.
  Qed.
  Lemma valid_inf_system_trace_rel
        {Λ : language} {M} (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (iex : inf_execution_trace Λ) (iatr : inf_auxiliary_trace M) :
    valid_inf_system_trace φ ex atr iex iatr → φ ex atr.
  Proof. inversion 1; done. Qed.

  Lemma crdt_main_rel_always_ternary
        (ex : execution_trace aneris_lang) (iex : inf_execution_trace aneris_lang)
        (atr : auxiliary_trace (aneris_to_trace_model (GCounterM gcdata))) :
    valid_inf_exec ex iex →
    continued_simulation crdt_main_rel ex atr →
    ∃ imtr,
       always3
          crdt_main_rel_ternary
          (locs_of_trace ex) ex atr (locs_of_inf_trace ex iex) iex imtr.
  Proof.
    intros Hvl Hcs.
    specialize (continued_simulation_rel _ _ _ Hcs) as (Hst & _ & _ & _).
    pose proof (produced_inf_aux_trace_valid_inf _ _  _ Hst Hcs iex Hvl) as Hvisf.
    clear Hst.
    exists (produce_inf_aux_trace _ ex atr Hcs iex Hvl).
    pose proof (valid_inf_system_trace_length _ _ _ _ _ Hvisf) as Hlen.
    apply (valid_inf_system_trace_mono _ crdt_main_rel) in Hvisf; last first.
    { apply continued_simulation_rel. }
    revert Hlen Hvisf.
    generalize (produce_inf_aux_trace _ ex atr Hcs iex Hvl); intros iatr.
    clear Hcs.
    revert ex iex atr iatr Hvl.
    cofix IH; intros ex iex atr iatr Hvl Hlen Hvisf.
    constructor; [| | |].
    - apply valid_inf_system_trace_rel in Hvisf; done.
    - apply locs_of_inf_trace_length.
    - eapply inflist_same_length_trans; done.
    - simpl.
      intros ?????????
             (?&?&?&?&?&?)%locs_of_inf_trace_cons_inv
             -> ->; simplify_eq.
      apply (IH (_ :tr[_]: _)).
      + apply traces.valid_inf_exec_adjust; done.
      + rewrite -inflist_same_length_cons; done.
      + apply (valid_inf_system_trace_take_drop 1) in Hvisf; done.
  Qed.

  Lemma eventually_sent_eventually_exists_loc_one i ex iex mtr imtr :
    i < GClen gcdata →
    valid_inf_exec ex iex →
    eventually (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []) ex iex →
    always3 crdt_main_rel_ternary (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr →
    eventually3
       (always3 (λ locs _ _ _ _ _, ∃ l, (trace_last locs) !! i = Some (Some l)))
       (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr.
  Proof.
    intros Hi Hvex Hev Hal.
    apply eventually_take_drop in Hev as [n Hev].
    assert ((always (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []))
               (ex +trl+ inflist_take n iex) (inflist_drop n iex)) as Hev'.
    { apply always_take_drop; intros k.
      destruct (events_of_trace_app
                   (sendonEV (ith_sa i))
                   (ex +trl+ inflist_take n iex)
                   (inflist_take k (inflist_drop n iex))) as (evs & ? & -> & _).
      { rewrite trace_append_list_assoc -inflist_take_add.
        eapply valid_inf_exe_valid_exec; eapply valid_inf_exe_take_drop; done. }
      intros []%app_eq_nil; simplify_eq. }
    clear Hev.
    apply eventually3_take_drop; exists n.
    split; last by eapply always3_inflist_same_length; eauto.
    apply (always3_unroll_n _ n) in Hal.
    apply always3_take_drop; intros k.
    split; last by eapply always3_inflist_same_length; eauto.
    apply (always3_unroll_n _ k), always3_holds in Hal.
    apply (always_unroll_n _ k), always_holds in Hev'.
    revert Hal Hev'.
    rewrite !trace_append_list_assoc -!inflist_take_add.
    intros Hal Hev.
    destruct Hal as (_&_&_& (sevss & Hlen & Hsevs) &_).
    specialize (Hsevs i Hi) as (sevs & ? & ? & Hlocs).
    rewrite list_lookup_total_alt in Hlocs.
    revert Hlocs.
    rewrite locs_of_inf_trace_take locs_of_trace_last.
    destruct (lookup_lt_is_Some_2 (locs_of_trace_now (ex +trl+ inflist_take (n + k) iex)) i)
      as [ol Hol].
    { rewrite locs_of_trace_now_length; done. }
    rewrite Hol; simpl.
    destruct ol; first by eauto.
    intros [? ?]; simplify_eq.
  Qed.

  Lemma eventually_sent_eventually_exists_loc_all ex iex mtr imtr :
    (∀ i, i < GClen gcdata →
          eventually (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []) ex iex) →
    valid_inf_exec ex iex →
    always3 crdt_main_rel_ternary (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr →
    eventually3
       (λ locs ex' mtr' ilocs' iex' imtr',
          ∀ (j : fin (S (GClen gcdata))),
             always3 (λ locs' ex'' mtr'' ilocs'' iex'' imtr'',
                      match fin_to_nat j with
                      | 0 => crdt_main_rel_ternary locs' ex'' mtr'' ilocs'' iex'' imtr''
                      | S k => ∃ l, (trace_last locs') !! k = Some (Some l)
                      end) locs ex' mtr' ilocs' iex' imtr')
       (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr.
  Proof.
    intros Hev Hvex Hal.
    apply eventually3_forall_combine.
    intros j.
    destruct (fin_to_nat j) as [|j'] eqn:Hj'.
    - pose proof (always3_inflist_same_length _ _ _ _ _ _ _ Hal) as [? ?].
      apply holds_eventually3; done.
    - assert (j' < GClen gcdata).
      { assert (S j' < S (GClen gcdata)) by by rewrite -Hj'; apply fin_to_nat_lt. lia. }
      apply eventually_sent_eventually_exists_loc_one; auto.
  Qed.

  Lemma eventually_sent_eventually_allocated_helper len locs ex mtr ilocs iex imtr :
  (∀ j : fin (S len),
     always3
       (λ locs' ex'' mtr'' ilocs'' iex'' imtr'',
          match fin_to_nat j with
          | 0 => crdt_main_rel_ternary locs' ex'' mtr'' ilocs'' iex'' imtr''
          | S k => ∃ l : loc, trace_last locs' !! k = Some (Some l)
        end) locs ex mtr ilocs iex imtr) →
  ∃ lcssg : {lcs : list loc | length lcs = len},
     take len (trace_last locs) = Some <$> `lcssg ∧
     always3 crdt_main_rel_ternary locs ex mtr ilocs iex imtr.
  Proof.
    intros Hex.
    induction len as [|n IHn].
    - exists (exist (λ l, length l = 0) (@nil loc) eq_refl).
      rewrite take_0 /=.
      split; first done.
      specialize (Hex 0%fin); done.
    - destruct IHn as [[lcs Hlcslen] [Hlcs1 Hlcs2]].
      { intros j.
        assert (fin_to_nat j < S (S n)) as Hlt.
        { etrans; first apply fin_to_nat_lt; lia. }
        specialize (Hex (nat_to_fin Hlt)).
        eapply always3_mono; last apply Hex.
        clear.
        rewrite fin_to_nat_to_fin; done. }
      assert (S n < S (S n)) as Hlt by lia.
      specialize (Hex (nat_to_fin Hlt)).
      apply always3_holds in Hex.
      rewrite fin_to_nat_to_fin in Hex.
      destruct Hex as [l Hl].
      assert (length (lcs ++ [l]) = S n) as Hlcslen'.
      { rewrite app_length Hlcslen; simpl; lia. }
      exists (exist _ (lcs ++ [l]) Hlcslen').
      split; last done.
      erewrite take_S_r; last by eauto.
      rewrite Hlcs1 fmap_app; simpl; done.
  Qed.

  Lemma eventually_sent_eventually_allocated_helper' locs ex mtr ilocs iex imtr :
    length (trace_last locs) = GClen gcdata →
  (∀ j : fin (S (GClen gcdata)),
     always3
       (λ locs' ex'' mtr'' ilocs'' iex'' imtr'',
          match fin_to_nat j with
          | 0 => crdt_main_rel_ternary locs' ex'' mtr'' ilocs'' iex'' imtr''
          | S k => ∃ l : loc, trace_last locs' !! k = Some (Some l)
        end) locs ex mtr ilocs iex imtr) →
  ∃ lcssg : {lcs : list loc | length lcs = GClen gcdata},
     trace_last locs = Some <$> `lcssg ∧
     always3 crdt_main_rel_ternary locs ex mtr ilocs iex imtr.
  Proof.
    intros Hlen Hex.
    rewrite -(firstn_all (trace_last locs)) Hlen.
    apply eventually_sent_eventually_allocated_helper; done.
  Qed.

  Lemma eventually_sent_eventually_allocated ex iex mtr imtr :
    (∀ i, i < GClen gcdata →
          eventually (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []) ex iex) →
    valid_inf_exec ex iex →
    always3 crdt_main_rel_ternary (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr →
    ∃ lcs : list loc,
       length lcs = GClen gcdata ∧
       eventually3
          (λ locs ex' mtr' ilocs' iex' imtr',
           (trace_last locs = Some <$> lcs) ∧
           always3 crdt_main_rel_ternary locs ex' mtr' ilocs' iex' imtr')
          (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr.
  Proof.
    intros Hev Hvex Hal.
    cut (∃ lcssg : {lcs : list loc | length lcs = GClen gcdata},
             eventually3
                (λ locs ex' mtr' ilocs' iex' imtr',
                 (trace_last locs = Some <$> `lcssg) ∧
                 always3 crdt_main_rel_ternary locs ex' mtr' ilocs' iex' imtr')
                (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr).
    { intros [[? ?] ?]; eauto. }
    apply eventually3_exists.
    epose proof (eventually_sent_eventually_exists_loc_all _ _ _ _ Hev Hvex Hal) as Hex.
    apply eventually3_take_drop in Hex as [n [Hex [Hilen1 Hilen2]]].
    apply eventually3_take_drop.
    exists n; split; last done.
    apply eventually_sent_eventually_allocated_helper'; last done.
    rewrite locs_of_inf_trace_take locs_of_trace_last locs_of_trace_now_length; done.
  Qed.

  Definition crdt_main_rel_locs_resolved (locs : list loc) (ex: execution_trace aneris_lang)
             (mtr : finite_trace (GCounterM gcdata) ())
             (iex: inf_execution_trace aneris_lang)
             (imtr : inflist (() * GCounterM gcdata))  : Prop :=
    valid_model_fin_trace mtr ∧
    gcounter_values_related_now_locs_resolved locs (trace_last ex) (trace_last mtr) ∧
    send_evs_rel_locs_resolved locs ex ∧
    receive_evs_rel_locs_resolved locs ex.

  Definition monotone_from_now_on locs ex iex :=
    (always (λ ex' _,
             ∃ l, ex' = ex +trl+ l ∧
                  gcounter_monotone_locs_resolved locs (trace_last ex :: map snd l)) ex iex).

  (* TODO: put in aneris *)

  Lemma monotone_from_now_on_unroll_n n locs ex iex :
    monotone_from_now_on locs ex iex →
    monotone_from_now_on locs (ex +trl+ inflist_take n iex) (inflist_drop n iex).
  Proof.
    intros Hfno.
    apply always_take_drop; intros m.
    apply (always_unroll_n _ n) in Hfno.
    apply (always_unroll_n _ m) in Hfno.
    apply always_holds in Hfno.
    destruct Hfno as [l [Hl Hgms]].
    rewrite Hl.
    rewrite !trace_append_list_assoc -!inflist_take_add in Hl.
    apply trace_append_list_inj2 in Hl.
    rewrite inflist_take_add in Hl.
    simplify_eq.
    eexists _; split.
    { rewrite !trace_append_list_assoc; done. }
    intros i j ?????.
    apply (Hgms (length (inflist_take n iex) + i) (length (inflist_take n iex) + j)).
    - lia.
    - destruct i as [|i]; simpl in *.
      + rewrite map_app (lookup_app_l (_ :: _)) /=; last by rewrite map_length /=; lia.
        rewrite Nat.add_0_r.
        rewrite trace_last_of_append_list_map //.
      + rewrite Nat.add_comm /= Nat.add_comm.
        rewrite map_app lookup_app_r; last by rewrite map_length; lia.
        rewrite map_length Nat.add_comm Nat.add_sub; done.
    - destruct j as [|j]; simpl in *.
      + rewrite map_app (lookup_app_l (_ :: _)); last by rewrite /= map_length /=; lia.
        rewrite Nat.add_0_r.
        rewrite trace_last_of_append_list_map; done.
      + rewrite Nat.add_comm /= Nat.add_comm.
        rewrite map_app lookup_app_r; last by rewrite map_length; lia.
        rewrite map_length Nat.add_comm Nat.add_sub; done.
  Qed.

  Definition closed_model_relation locs ex mtr iex imtr :=
    (monotone_from_now_on locs ex iex) ∧
    always2 (crdt_main_rel_locs_resolved locs) ex mtr iex imtr.

  Lemma eventually_sent_eventually_locs_resolved ex iex mtr imtr :
    (∀ i, i < GClen gcdata →
          eventually (λ ex' _, events_of_trace (sendonEV (ith_sa i)) ex' ≠ []) ex iex) →
    valid_inf_exec ex iex →
    always3 crdt_main_rel_ternary (locs_of_trace ex) ex mtr (locs_of_inf_trace ex iex) iex imtr →
    ∃ locs, length locs = GClen gcdata ∧ eventually2 (closed_model_relation locs) ex mtr iex imtr.
  Proof.
    intros Hev Hvl Hal3.
    edestruct (eventually_sent_eventually_allocated ex iex mtr imtr) as (locs & Hlocslen & Hal);
      [done|done|done|].
    exists locs; split; first done.
    apply eventually3_take_drop in Hal as [n [[Hex1 Hex2] [Hilen1 Hilen2]]].
    apply eventually2_take_drop.
    exists n; split; last done.
    split.
    - apply always_take_drop; intros k.
      apply (always3_unroll_n _ n), (always3_unroll_n _ k), always3_holds in Hal3.
      rewrite !trace_append_list_assoc -!inflist_take_add in Hal3.
      rewrite !locs_of_inf_trace_take in Hal3.
      apply crdt_main_rel_ternary_crdt_main_rel in Hal3.
      apply crdt_main_rel_monotone in Hal3.
      rewrite !inflist_take_add -!trace_append_list_assoc in Hal3.
      pose proof (locs_of_inf_trace_less_defined _ _ Hvl) as Hld.
      apply (always_unroll_n _ n), (always_unroll_n _ k), always_holds in Hld.
      eexists _; split; first reflexivity.
      eapply (gcounter_monotone_resolve_locs
                 locs
                 (ex +trl+ inflist_take n iex)
                 (inflist_take
                     k
                     (locs_of_inf_trace (ex +trl+ inflist_take n iex) (inflist_drop n iex)))).
      + apply inflist_take_of_same_length, locs_of_inf_trace_length.
      + done.
      + eapply valid_inf_exe_valid_exec.
        do 2 apply valid_inf_exe_take_drop; done.
      + rewrite -locs_of_inf_trace_take; done.
      + rewrite !locs_of_inf_trace_take.
        rewrite trace_append_list_assoc -inflist_take_add.
        rewrite trace_append_list_assoc in Hld.
        rewrite -inflist_take_add in Hld.
        rewrite !locs_of_inf_trace_take in Hld.
        done.
      + rewrite !locs_of_inf_trace_take. done.
    - apply always2_take_drop; intros k; split; last by apply inflist_same_length_drop.
      apply (always3_unroll_n _ k), always3_holds in Hex2.
      pose proof (locs_of_inf_trace_less_defined _ _ Hvl) as Hld.
      apply (always_unroll_n _ n), (always_unroll_n _ k), always_holds in Hld.
      eapply trace_append_list_steps_rtc_nl in Hld; [|done|done].
      revert Hld; rewrite rt_rtc_same.
      rewrite !trace_append_list_assoc -!inflist_take_add.
      rewrite !trace_append_list_assoc -!inflist_take_add in Hex2.
      intros Hld.
      apply locs_all_defined in Hld.
      destruct Hex2 as (_ & vmf & Hvrel%trace_forall3_last & Hsevs & Hrevs).
      rewrite Hld in Hvrel, Hrevs, Hsevs.
      split_and!.
      + done.
      + apply gcounter_values_related_now_resolve_locs; auto.
      + apply send_evs_rel_resolve_locs; auto.
      + apply receive_evs_rel_resolve_locs; auto.
  Qed.

End crdt_main_rel.

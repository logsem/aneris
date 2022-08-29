From iris.algebra Require Import auth excl csum gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Import gset_map.
From aneris.prelude Require Import time.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.examples.gcounter_convergence Require Import crdt_code crdt_model vc.

Record GCData : Type := {
  gcd_addr_list : list socket_address;
  gcd_addr_list_NoDup_ips : NoDup (ip_of_address <$> gcd_addr_list);
  gcd_addr_list_nonSys : ∀ i sa, gcd_addr_list !! i = Some sa → ip_of_address sa ≠ "system";
}.

Lemma gcd_addr_list_NoDup gcdata : NoDup (gcd_addr_list gcdata).
Proof. eapply NoDup_fmap_1; apply gcdata. Qed.

Notation GClen gcdata := (length (gcd_addr_list gcdata)).

Canonical Structure vector_clockO n := leibnizO (vector_clock n).
Canonical Structure crdt_stateO n := leibnizO (crdt_state n).

Definition GCounterM gcdata : Model := model _ (λ x y, CrdtNext x tt y) (initial_crdt_state (GClen gcdata)).

Notation PrinGC c := (principal vc_le c).

Notation crdt_stateUR gcdata :=
  (authUR (gmapUR nat (@monotoneUR (vector_clockO (GClen gcdata)) vc_le))).
Notation crdt_locsUR := (authUR (gmapUR nat (csumR (exclR unitO) (agreeR (leibnizO loc))))).
Notation sendevO gcdata :=
  (prodO natO (prodO (vector_clockO (GClen gcdata)) (vector_clockO (GClen gcdata)))).
Notation crdt_sendEVUR gcdata := (authUR (gmapUR nat (exclR (listO (sendevO gcdata))))).
Notation crdt_recEVUR gcdata :=
  (authUR (gmapUR nat (exclR (listO (vector_clockO (GClen gcdata)))))).

Class GCounterG Σ (gcdata : GCData) := {
  GCG_view_monoΣ :> inG Σ (crdt_stateUR gcdata);
  GCG_locΣ :> inG Σ crdt_locsUR;
  GCG_sendEVΣ :> inG Σ (crdt_sendEVUR gcdata);
  GCG_recEVΣ :> inG Σ (crdt_recEVUR gcdata);
  GCG_vcs_name : gname;
  GCG_locs_name : gname;
  GCG_sendevs_name : gname;
  GCG_recevs_name : gname;
}.

Class GCounterPreG Σ (gcdata : GCData) := {
  GCPG_view_monoΣ :> inG Σ (crdt_stateUR gcdata);
  GCPG_locΣ :> inG Σ crdt_locsUR;
  GCPG_sendEVΣ :> inG Σ (crdt_sendEVUR gcdata);
  GCPG_recEVΣ :> inG Σ (crdt_recEVUR gcdata);
}.

Definition GCounterΣ (gcdata : GCData) :=
  #[GFunctor (crdt_stateUR gcdata); GFunctor crdt_locsUR;
   GFunctor (crdt_sendEVUR gcdata); GFunctor (crdt_recEVUR gcdata)].

Global Instance subG_GCounterPreG Σ gcdata : subG (GCounterΣ gcdata) Σ → GCounterPreG Σ gcdata.
Proof. constructor; solve_inG. Qed.

Section Resources.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.

  Notation vector_clock := (vector_clock (GClen gcdata)).
  Notation crdt_state := (crdt_state (GClen gcdata)).

  Definition GCounters (st : crdt_state) : iProp Σ :=
    own (A := crdt_stateUR gcdata) GCG_vcs_name (● ((λ c, PrinGC c) <$> list_to_gmap id st)).

  Definition GCounterSnapShot (i : nat) (c : vector_clock) : iProp Σ :=
    own (A := crdt_stateUR gcdata) GCG_vcs_name (◯ {[i := PrinGC c]}).

  Definition oloc_to_one_shot (ol : option loc) : csum (excl unit) (agree loc) :=
    from_option (λ l, Cinr (to_agree l)) (Cinl (Excl ())) ol.

  Definition GClocations (l : list (option loc)) :=
    own (A:= crdt_locsUR) GCG_locs_name (● (list_to_gmap oloc_to_one_shot l)).

  Definition GCunallocated (i : nat) := own GCG_locs_name (◯ {[ i := Cinl (Excl ())]}).

  Definition GCallocated (i : nat) (l : loc) := own GCG_locs_name (◯ {[ i := Cinr (to_agree l)]}).

  Definition loc_coherence (i : nat) (ol : option loc) (vc : vector_clock) : iProp Σ :=
    match ol with
    | None => alloc_evs (StringOfZ i) [] ∗
              ⌜vc = (vreplicate (GClen gcdata) 0)⌝
    | Some l =>
        ∃ a,
          ⌜gcd_addr_list gcdata !! i = Some a⌝ ∗
          (∃ σ h, ⌜valid_allocObs (ip_of_address a) l σ h⌝ ∗
                   alloc_evs (StringOfZ i)
                   [allocObs (ip_of_address a) (StringOfZ i) l
                             (vector_clock_to_val (vreplicate (GClen gcdata) 0)) σ h]) ∗
          l ↦[ip_of_address a] (vector_clock_to_val vc)
    end.

  Definition locations_coherence (locs : list (option loc)) (st : crdt_state) : iProp Σ :=
    [∗ list] i ↦ ol; vc ∈ locs; st, loc_coherence i ol vc.

  Definition sendevs_auth (sevss : list (list (nat * (vector_clock * vector_clock)))) : iProp Σ :=
    own GCG_sendevs_name (● list_to_gmap Excl sevss).

  Definition sendevs_frag (i : nat) (sevs : list (nat * (vector_clock * vector_clock))) : iProp Σ :=
    own GCG_sendevs_name (◯ {[ i := Excl sevs ]}).

  Definition send_events_correspond (sa : socket_address) (l : loc)
             (ev : EventObservation aneris_lang)
             (sev : nat * (vector_clock * vector_clock)) : Prop :=
    ∃ sa' σ h sh skts skt r s,
      gcd_addr_list gcdata !! sev.1 = Some sa' ∧
      vc_is_ser (vector_clock_to_val sev.2.2) s ∧
      valid_sendonObs sa σ sh skts skt r ∧
      ev = sendonObs sa σ sh s sa' skt ∧
      σ.(state_heaps) !! (ip_of_address sa) = Some h ∧
      h !! l = Some (vector_clock_to_val sev.2.1).

  Definition sendevs_valid (sevss : list (nat * (vector_clock * vector_clock))) : Prop :=
    ∀ i j sev sev',
      sevss !! i = Some sev →
      j < i →
      sevss !! j = Some sev' →
      sev'.1 = sev.1 →
      vc_le sev'.2.1 sev.2.2.

  Definition sendev_coh (i : nat) (ol : option loc)
             (sevs : list (nat * (vector_clock * vector_clock))) : iProp Σ :=
    ∃ sa,
      ⌜gcd_addr_list gcdata !! i = Some sa⌝ ∧ ⌜sendevs_valid sevs⌝ ∧
      ([∗ list] sev ∈ sevs, GCounterSnapShot i sev.2.1) ∗
      match ol with
      | Some l => ∃ evs, sendon_evs sa evs ∗ ⌜Forall2 (send_events_correspond sa l) evs sevs⌝
      | None => sendon_evs sa [] ∧ ⌜sevs = []⌝
      end.

  Definition sendevs_coherence (locs : list (option loc))
             (sevss : list (list (nat * (vector_clock * vector_clock)))) : iProp Σ :=
    [∗ list] i ↦ ol; sevs ∈ locs; sevss, sendev_coh i ol sevs.

  Definition recevs_auth (evss : list (list vector_clock)) : iProp Σ :=
    own GCG_recevs_name (● list_to_gmap Excl evss).

  Definition recevs_frag (i : nat) (evs : list vector_clock) : iProp Σ :=
    own GCG_recevs_name (◯ {[ i := Excl evs ]}).

  Definition rec_events_correspond (sa : socket_address)
             (ev : EventObservation aneris_lang)
             (rev : vector_clock) : Prop :=
    ∃ σ sh skts skt msg r,
      vc_is_ser (vector_clock_to_val rev) (m_body msg) ∧
      valid_receiveonObs sa σ sh msg skts skt r ∧
      ev = receiveonObs sa σ sh msg skts skt r.

  Definition recev_coh (i : nat) (revs : list vector_clock) : iProp Σ :=
    ∃ sa evs, ⌜gcd_addr_list gcdata !! i = Some sa⌝ ∧
      (∀ rev j, ⌜S j < length revs⌝ → ⌜revs !! j = Some rev⌝ → GCounterSnapShot i rev) ∗
      (⌜evs ≠ []⌝ → ∃ l, GCallocated i l) ∗
      receiveon_evs sa evs ∗ ⌜Forall2 (rec_events_correspond sa) evs revs⌝.

  Definition recevs_coherence (revss : list (list vector_clock)) : iProp Σ :=
    [∗ list] i ↦ sa; revs ∈ gcd_addr_list gcdata; revss,
       (∀ rev j, ⌜S j < length revs⌝ → ⌜revs !! j = Some rev⌝ → GCounterSnapShot i rev) ∗
       ∃ evs,
         (⌜evs ≠ []⌝ → ∃ l, GCallocated i l) ∗
         receiveon_evs sa evs ∗ ⌜Forall2 (rec_events_correspond sa) evs revs⌝.

  (* Properties *)

  Lemma GCounterSnapShot_le (i : fin (GClen gcdata)) vc st :
    GCounterSnapShot i vc -∗ GCounters st -∗ ⌜vc_le vc (st !!! i)⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H2 H1") as %[Hv1 Hv2]%auth_both_valid_discrete.
    apply singleton_included_l in Hv1 as (vc' & Hvc'1 & Hvc'2).
    rewrite /= lookup_fmap list_to_gmap_lookup in Hvc'1.
    destruct ((vec_to_list st) !! (fin_to_nat i)) as [vc''|] eqn:Heq; last by inversion Hvc'1.
    apply vlookup_lookup in Heq as ->.
    apply Some_equiv_inj in Hvc'1.
    revert Hvc'2; rewrite -Hvc'1 Some_included_total principal_included; done.
  Qed.

  Lemma GCounters_update (i : fin (GClen gcdata)) vc' (st : crdt_state):
    vc_le (st !!! i) vc' → GCounters st ==∗ GCounters (vinsert i vc' st) ∗ GCounterSnapShot i vc'.
  Proof.
    iIntros (Hle) "Ho".
    rewrite /GCounterSnapShot /GCounters.
    iMod (own_update _ _ (● _ ⋅ ◯ _) with "Ho") as "[$ $]"; last done.
    apply auth_update_alloc.
    rewrite vec_to_list_insert -list_to_gmap_insert;
      last by rewrite vec_to_list_length; apply fin_to_nat_lt.
    rewrite fmap_insert.
    eapply insert_alloc_local_update; [|done|].
    { rewrite lookup_fmap list_to_gmap_lookup.
      pose proof (eq_refl : st !!! i = st !!! i) as Hlu.
      apply vlookup_lookup in Hlu as ->; done. }
    apply monotone_local_update_grow; done.
  Qed.

  Lemma get_GCounterSnapShot_weaken (i : fin (GClen gcdata)) st vc :
    vc_le vc (st !!! i) →
     GCounters st ==∗ GCounters st ∗ GCounterSnapShot i vc.
  Proof.
    iIntros (Hle) "Ho".
    rewrite /GCounterSnapShot /GCounters.
    iMod (own_update _ _ (● _ ⋅ ◯ _) with "Ho") as "[$ $]"; last done.
    apply auth_update_alloc.
    rewrite -{2}(vlookup_insert_self i st).
    rewrite vec_to_list_insert -list_to_gmap_insert;
      last by rewrite vec_to_list_length; apply fin_to_nat_lt.
    rewrite fmap_insert.
    eapply insert_alloc_local_update; [|done|].
    { rewrite lookup_fmap list_to_gmap_lookup.
      pose proof (eq_refl : st !!! i = st !!! i) as Hlu.
      apply vlookup_lookup in Hlu as ->; done. }
    apply monotone_local_update_get_frag; done.
  Qed.

  Lemma get_GCounterSnapShot (i : fin (GClen gcdata)) st :
     GCounters st ==∗ GCounters st ∗ GCounterSnapShot i (st !!! i).
  Proof. rewrite -{2}(vlookup_insert_self i st); apply GCounters_update; done. Qed.

  Lemma locations_is_unallocated i locs :
    GClocations locs -∗ GCunallocated i -∗ ⌜locs !! i = Some None⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2")
      as %[(z & Hz1 & Hz2)%singleton_included_l ?]%auth_both_valid_discrete.
    rewrite list_to_gmap_lookup in Hz1.
    destruct (locs !! i) as [[]|]; simpl in *; [|done|by inversion Hz1].
    revert Hz2; rewrite -Hz1 Some_included; intros [Hinc|Hinc]; first by inversion Hinc.
    apply csum_included in Hinc as [|[(?&?&?&?&?&?)|(?&?&?&?&?)]]; done.
  Qed.

  Lemma locations_is_allocated i locs l :
    GClocations locs -∗ GCallocated i l -∗ ⌜locs !! i = Some (Some l)⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2")
      as %[(z & Hz1 & Hz2)%singleton_included_l ?]%auth_both_valid_discrete.
    rewrite list_to_gmap_lookup in Hz1.
    destruct (locs !! i) as [[]|]; simpl in *; [| |by inversion Hz1].
    - revert Hz2; rewrite -Hz1 Some_included; intros [Hinc|Hinc].
      + apply Cinr_inj, to_agree_inj, leibniz_equiv in Hinc as <-; done.
      + apply Cinr_included, to_agree_included, leibniz_equiv in Hinc as <-; done.
    - revert Hz2; rewrite -Hz1 Some_included; intros [Hinc|Hinc]; first by inversion Hinc.
      apply csum_included in Hinc as [|[(?&?&?&?&?&?)|(?&?&?&?&?)]]; done.
  Qed.

  Lemma locations_alloc i locs l :
    GClocations locs -∗ GCunallocated i ==∗ GClocations (<[i := Some l]> locs) ∗ GCallocated i l.
  Proof.
    iIntros "Hlocs Hua".
    iDestruct (locations_is_unallocated with "Hlocs Hua") as %Hlu.
    iMod (own_update_2 _ _ _ (● _ ⋅ ◯ _) with "Hlocs Hua") as "[$ $]"; last done.
    apply auth_update.
    rewrite -list_to_gmap_insert; last by apply lookup_lt_is_Some_1; eauto.
    apply: singleton_local_update; first by rewrite list_to_gmap_lookup Hlu.
    apply exclusive_local_update; done.
  Qed.

  Lemma locations_coherence_length locs st :
    locations_coherence locs st -∗ ⌜length locs = GClen gcdata⌝.
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_length with "H") as %Hlen.
    rewrite vec_to_list_length in Hlen; done.
  Qed.

  Lemma locations_coherence_insert_acc (i : fin (GClen gcdata)) locs ol st :
    locs !! (fin_to_nat i) = Some ol →
    locations_coherence locs st -∗
    loc_coherence i ol (st !!! i) ∗
    (∀ ol' vc,
        loc_coherence i ol' vc -∗
        locations_coherence (<[fin_to_nat i := ol']> locs) (vinsert i vc st)).
  Proof.
    iIntros (Hiol) "Hlc"; rewrite /locations_coherence.
    iDestruct (big_sepL2_insert_acc with "Hlc") as "[$ Hlc]";
      [apply Hiol|by apply vlookup_lookup|].
    setoid_rewrite vec_to_list_insert; done.
  Qed.

  Lemma sendevs_agree sevss i sevs :
    sendevs_auth sevss -∗ sendevs_frag i sevs -∗ ⌜sevss !! i = Some sevs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv1 Hv2]%auth_both_valid_discrete.
    apply singleton_included_l in Hv1 as (vc' & Hvc'1 & Hvc'2).
    rewrite /= list_to_gmap_lookup in Hvc'1.
    apply leibniz_equiv in Hvc'1.
    specialize (Hv2 i); rewrite /= list_to_gmap_lookup in Hv2.
    destruct (sevss !! i) as [vc''|] eqn:Heq; last by inversion Hvc'1.
    destruct vc'; last by simplify_eq/=.
    simplify_eq/=.
    apply Excl_included, leibniz_equiv in Hvc'2; simplify_eq; done.
  Qed.

  Lemma sendevs_update sevss i sevs sevs' :
    sendevs_auth sevss -∗
    sendevs_frag i sevs ==∗
    sendevs_auth (<[i := sevs']>sevss) ∗ sendevs_frag i sevs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (sendevs_agree with "H1 H2") as %Hlu.
    rewrite /sendevs_auth /sendevs_frag.
    iMod (own_update_2 _ _ _ (● _ ⋅ ◯ _) with "H1 H2") as "[$ $]"; last done.
    apply auth_update.
    rewrite -list_to_gmap_insert; last by apply lookup_lt_Some in Hlu.
    eapply singleton_local_update; first by rewrite list_to_gmap_lookup Hlu.
    apply exclusive_local_update; done.
  Qed.

  Lemma recevs_agree revss i revs :
    recevs_auth revss -∗ recevs_frag i revs -∗ ⌜revss !! i = Some revs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv1 Hv2]%auth_both_valid_discrete.
    apply singleton_included_l in Hv1 as (vc' & Hvc'1 & Hvc'2).
    rewrite /= list_to_gmap_lookup in Hvc'1.
    apply leibniz_equiv in Hvc'1.
    specialize (Hv2 i); rewrite /= list_to_gmap_lookup in Hv2.
    destruct (revss !! i) as [vc''|] eqn:Heq; last by inversion Hvc'1.
    destruct vc'; last by simplify_eq/=.
    simplify_eq/=.
    apply Excl_included, leibniz_equiv in Hvc'2; simplify_eq; done.
  Qed.

  Lemma recevs_update revss i revs revs' :
    recevs_auth revss -∗
    recevs_frag i revs ==∗
    recevs_auth (<[i := revs']>revss) ∗ recevs_frag i revs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (recevs_agree with "H1 H2") as %Hlu.
    rewrite /recevs_auth /recevs_frag.
    iMod (own_update_2 _ _ _ (● _ ⋅ ◯ _) with "H1 H2") as "[$ $]"; last done.
    apply auth_update.
    rewrite -list_to_gmap_insert; last by apply lookup_lt_Some in Hlu.
    eapply singleton_local_update; first by rewrite list_to_gmap_lookup Hlu.
    apply exclusive_local_update; done.
  Qed.

  Lemma sendevs_coherence_length locs sevss :
    sendevs_coherence locs sevss -∗ ⌜length locs = length sevss⌝.
  Proof. iApply big_sepL2_length. Qed.

  Lemma sendevs_coherence_insert_acc i locs ol sevss sevs :
    locs !! i = Some ol →
    sevss !! i = Some sevs →
    sendevs_coherence locs sevss -∗
    sendev_coh i ol sevs ∗
    (∀ ol' sevs',
        sendev_coh i ol' sevs' -∗
        sendevs_coherence (<[i := ol']> locs) (<[i := sevs']>sevss)).
  Proof.
    iIntros (Hiol Hsevs) "Hsc"; rewrite /sendevs_coherence.
    iDestruct (big_sepL2_insert_acc with "Hsc") as "[$ Hsc]";
      [apply Hiol|apply Hsevs|]; done.
  Qed.

  Lemma recevs_coherence_length revss :
    recevs_coherence revss -∗ ⌜length revss = GClen gcdata⌝.
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_length with "H") as %?; done.
  Qed.

  Lemma recevs_coherence_insert_acc i revss revs :
    revss !! i = Some revs →
    recevs_coherence revss -∗
    recev_coh i revs ∗
    (∀ revs',
        recev_coh i revs' -∗
        recevs_coherence (<[i := revs']>revss)).
  Proof.
    iIntros (Hrevs) "Hrc"; rewrite /recevs_coherence.
    iDestruct (recevs_coherence_length with "Hrc") as %Hlen.
    destruct (lookup_lt_is_Some_2 (gcd_addr_list gcdata) i) as [sa Hsa].
    { rewrite -Hlen; apply lookup_lt_is_Some_1; eauto. }
    iDestruct (big_sepL2_insert_acc with "Hrc") as "[[Hi1 Hi2] Hrc]";
      [apply Hsa|apply Hrevs|].
    iSplitL "Hi1 Hi2".
    - iDestruct "Hi2" as (?) "Hi2".
      iExists _, _; iSplit; first done.
      iFrame.
    - iIntros (revs').
      iSpecialize ("Hrc" $! sa revs').
      rewrite (list_insert_id (gcd_addr_list gcdata) i sa); last done.
      iDestruct 1 as (sa' ? Hsa') "(H1 & H2 & H3)".
      rewrite Hsa' in Hsa; simplify_eq.
      iApply "Hrc".
      iFrame; iExists _; iFrame.
  Qed.

  Lemma sendevs_valid_extend sevs sevs' trpl :
    (∀ sev, sev ∈ sevs → vc_le sev.2.1 trpl.2.2) →
    (∀ sev, sev ∈ sevs' → sev.1 ≠ trpl.1) →
    sendevs_valid (sevs ++ sevs') → sendevs_valid (sevs ++ sevs' ++ [trpl]).
  Proof.
    intros Hsevs Hsevs' Hvl.
    intros i j sev sev' Hisev Hij Hjsev' Hfst.
    destruct (decide (i < length (sevs ++ sevs'))) as [|Hnlt].
    - eapply Hvl; [|apply Hij| |done].
      + rewrite assoc_L lookup_app_l in Hisev; done.
      + rewrite assoc_L lookup_app_l in Hjsev'; [done|lia].
    - assert (i = length (sevs ++ sevs')) as ->.
      { eapply lookup_lt_Some in Hisev.
        rewrite !app_length in Hisev, Hnlt.
        rewrite !app_length; simpl in *;lia. }
      rewrite assoc_L lookup_app_r in Hisev; last lia.
      rewrite Nat.sub_diag in Hisev; simplify_eq/=.
      rewrite assoc_L lookup_app_l in Hjsev'; last lia.
      destruct (decide (j < length sevs)).
      + rewrite lookup_app_l in Hjsev'; last done.
        apply Hsevs; apply elem_of_list_lookup; eauto.
      + rewrite lookup_app_r in Hjsev'; last lia.
        exfalso; eapply Hsevs'; last by apply Hfst.
        apply elem_of_list_lookup; eauto.
  Qed.

End Resources.

Section Resources_alloc.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterPreG Σ gcdata}.

  Notation vector_clock := (vector_clock (GClen gcdata)).
  Notation crdt_state := (crdt_state (GClen gcdata)).

  Lemma Gcounter_init :
    ⊢ |==> ∃ γ, own (A := crdt_stateUR gcdata) γ
                    (● ((λ c, PrinGC c) <$> list_to_gmap id (initial_crdt_state (GClen gcdata)))).
  Proof.
    apply own_alloc.
    apply auth_auth_valid; intros ?.
    rewrite lookup_fmap list_to_gmap_lookup.
    destruct (vec_to_list (initial_crdt_state (GClen gcdata)) !! i) eqn:Heq; done.
  Qed.

  Lemma locations_init :
    ⊢ |==> ∃ γ, own γ (● list_to_gmap oloc_to_one_shot (replicate (GClen gcdata) None)) ∗
            [∗ list] i ∈ (seq 0 (GClen gcdata)), own γ (◯ {[i := Cinl (Excl ())]}).
  Proof.
    iIntros "".
    iMod (own_alloc (● list_to_gmap oloc_to_one_shot (replicate (GClen gcdata) None) ⋅
                     ◯ list_to_gmap oloc_to_one_shot (replicate (GClen gcdata) None)))
      as (γ) "[Hlocs Hua]".
    { apply auth_both_valid_2; last done.
      intros ?; rewrite list_to_gmap_lookup.
      destruct (replicate (GClen gcdata) None !! i) as [[]|]; done. }
    iModIntro; iExists _; iFrame "Hlocs".
    generalize 0; intros n.
    iInduction (GClen gcdata) as [|k IHk] "IH" forall (n); simpl; first done.
    rewrite list_to_gmap_go_cons insert_singleton_op; last by apply list_to_gmap_go_lookup_lt; lia.
    iDestruct "Hua" as "[$ Hua]".
    iApply "IH"; done.
  Qed.

  Lemma sendevs_init k :
    ⊢ |==> ∃ γ, own γ (● list_to_gmap_go 0 Excl
                        (replicate k (@nil (nat * (vector_clock * vector_clock))))) ∗
             [∗ list] i ∈ (seq 0 k),
               own γ (◯ {[i := Excl (@nil (nat * (vector_clock * vector_clock))) ]}).
  Proof.
    iIntros "".
    iMod (own_alloc (● list_to_gmap Excl (replicate k
                                            (@nil (nat * (vector_clock * vector_clock)))) ⋅
                     ◯ list_to_gmap Excl (replicate k
                                            (@nil (nat * (vector_clock * vector_clock))))))
      as (γ) "[Hevs Hua]".
    { apply auth_both_valid_2; last done.
      intros ?; rewrite list_to_gmap_lookup.
      destruct (replicate k [] !! i) as [[]|]; done. }
    iModIntro; iExists _; iFrame "Hevs".
    generalize 0; intros n.
    iInduction k as [|k IHk] "IH" forall (n); simpl; first done.
    rewrite list_to_gmap_go_cons insert_singleton_op; last by apply list_to_gmap_go_lookup_lt; lia.
    iDestruct "Hua" as "[$ Hua]".
    iApply "IH"; done.
  Qed.

  Lemma recevs_init k :
    ⊢ |==> ∃ γ, own γ (● list_to_gmap_go 0 Excl (replicate k (@nil vector_clock))) ∗
             [∗ list] i ∈ (seq 0 k), own γ (◯ {[i := Excl (@nil vector_clock) ]}).
  Proof.
    iIntros "".
    iMod (own_alloc (● list_to_gmap Excl (replicate k (@nil vector_clock)) ⋅
                     ◯ list_to_gmap Excl (replicate k (@nil vector_clock))))
      as (γ) "[Hevs Hua]".
    { apply auth_both_valid_2; last done.
      intros ?; rewrite list_to_gmap_lookup.
      destruct (replicate k [] !! i) as [[]|]; done. }
    iModIntro; iExists _; iFrame "Hevs".
    generalize 0; intros n.
    iInduction k as [|k IHk] "IH" forall (n); simpl; first done.
    rewrite list_to_gmap_go_cons insert_singleton_op; last by apply list_to_gmap_go_lookup_lt; lia.
    iDestruct "Hua" as "[$ Hua]".
    iApply "IH"; done.
  Qed.

End Resources_alloc.

Section Resources_alloc.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.

  Lemma locations_coh_init_helper k n :
    ([∗ list] i ∈ seq k n, alloc_evs (StringOfZ (i : nat)) []) -∗
    [∗ list] i↦ol;vc ∈ (replicate n None); (vreplicate n (vreplicate (GClen gcdata) 0)),
      loc_coherence (k + i) ol vc.
  Proof.
    iIntros "H".
    rewrite big_sepL2_replicate_l /=; last by rewrite vec_to_list_length.
    rewrite vec_to_list_replicate.
    iInduction n as [|n] "IH" forall (k); simpl; first done.
    rewrite Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iSplit; first done.
    iSpecialize ("IH" with "H").
    iApply (big_sepL_impl with "IH").
    iIntros "!#" (??) "? ?".
    rewrite plus_Snm_nSm; iFrame.
  Qed.

  Lemma locations_coh_init :
    ([∗ list] i ∈ seq 0 (GClen gcdata), alloc_evs (StringOfZ (i : nat)) []) -∗
    locations_coherence (replicate (GClen gcdata) None) (initial_crdt_state (GClen gcdata)).
  Proof. iApply locations_coh_init_helper. Qed.

  Lemma sendevs_coh_init :
    ([∗ list] a ∈ gcd_addr_list gcdata, sendon_evs a []) -∗
    sendevs_coherence (replicate (GClen gcdata) None) (replicate (GClen gcdata) []).
  Proof.
    iIntros "H".
    rewrite /sendevs_coherence.
    rewrite big_sepL2_replicate_l /=; last by rewrite replicate_length.
    rewrite -(const_fmap (λ _, [])); last done.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "H").
    iIntros "!#" (?? ?) "H".
    iExists _; simpl; iFrame; done.
  Qed.

  Lemma recevs_coh_init :
    ([∗ list] a ∈ gcd_addr_list gcdata, receiveon_evs a []) -∗
    recevs_coherence (replicate (GClen gcdata) []).
  Proof.
    iIntros "H".
    rewrite /recevs_coherence.
    rewrite big_sepL2_replicate_r; last done.
    iApply (big_sepL_impl with "H").
    iIntros "!#" (?? ?) "H"; simpl.
    iSplit.
    { iIntros (? ? ?); lia. }
    iExists _; simpl; iFrame.
    iSplit; [by iIntros (?)|done].
  Qed.

End Resources_alloc.

Section Sockets.
  Context `{!anerisG (crdt_model gcdata) Σ, !GCounterG Σ gcdata}.
  Context (GCG_vcs_name : gname).

  Notation vector_clock := (vector_clock (GClen gcdata)).
  Notation crdt_state := (crdt_state (GClen gcdata)).

  Definition GCounter_socket_proto : socket_interp Σ :=
    (λ m,
     let mb := m_body m in
     ∃ (t : vector_clock) (i j : nat),
       ⌜vc_is_ser (vector_clock_to_val t) mb⌝
       ∧ ⌜gcd_addr_list gcdata !! i = Some (m_sender m)⌝
       ∧ ⌜gcd_addr_list gcdata !! j = Some (m_destination m)⌝
       ∧ ⌜i ≠ j⌝
       ∧ ⌜length t = GClen gcdata⌝
       ∧ GCounterSnapShot i t)%I.

End Sockets.

Section Global_invariant.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.
  Context (GCG_locs_name GCG_vcs_name : gname).

  Notation vector_clock := (vector_clock (GClen gcdata)).
  Notation crdt_state := (crdt_state (GClen gcdata)).

  Definition CvRDT_InvName := nroot .@ "CRDT".

  Definition Global_Inv :=
    inv CvRDT_InvName
        (∃ st locs sevss revss,
            frag_st st ∗ GCounters st ∗ GClocations locs ∗ sendevs_auth sevss ∗ recevs_auth revss ∗
            locations_coherence locs st ∗
            sendevs_coherence locs sevss ∗ recevs_coherence revss ∗
            ([∗ list] a ∈ gcd_addr_list gcdata,
                ∃ R T, a ⤳[true, true] (R, T) ∗ [∗ set] m ∈ R, GCounter_socket_proto m)).

End Global_invariant.

From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth.
From iris.base_logic Require Export own gen_heap.
From iris.base_logic.lib Require Import viewshifts saved_prop.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export tactics resources network notation.
Set Default Proof Using "Type".

Import Network.

Class distPreG Σ := DistPreG {
  distPre_invG :> invPreG Σ;
  distPre_mapG :> inG Σ (authR system_state_mapUR);
  distPre_heapG :> gen_heapPreG loc ground_lang.val Σ;
  (* network *)
  distPre_socketG :> gen_heapPreG socket_handle (socket * message_soup * message_soup) Σ;
  distPre_freeipsG :> inG Σ (authUR (gset_disjUR ip_address));
  distPre_freeportsG :> inG Σ (authUR (gmapUR ip_address (gset_disjUR port)));
  distPre_siG :> inG Σ socket_interpR;
  distPre_fixedG :> inG Σ (agreeR (gsetUR socket_address));
  distPre_savedPredG :> savedPredG Σ message
}.

Definition distΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc ground_lang.val;
      GFunctor (authR system_state_mapUR);
      gen_heapΣ socket_handle (socket * message_soup * message_soup);
      GFunctor (authUR (gset_disjUR ip_address));
      GFunctor (authUR (gmapUR ip_address (gset_disjUR port)));
      GFunctor socket_interpR;
      GFunctor (agreeR (gsetUR socket_address));
      savedPredΣ message
   ].

Global Instance subG_heapPreG {Σ} : subG distΣ Σ → distPreG Σ.
Proof. constructor; solve_inG. Qed.

Definition gen_heap_frag `{g : gen_heapG L V Σ} σ :=
  own (gen_heap_name g) (◯ to_gen_heap σ).

Lemma gen_heap_init_frag `{gen_heapPreG L V Σ} σ :
  ⊢ |==> ∃ g : gen_heapG L V Σ, gen_heap_ctx σ ∗ gen_heap_frag σ.
Proof.
  iMod (own_alloc (● to_gen_heap σ ⋅ ◯ to_gen_heap σ)) as (γh) "H".
  { apply auth_both_valid. split; auto. exact: to_gen_heap_valid. }
  iMod (own_alloc (A:=authR (gen_metaUR L))
                  (● to_gen_meta ∅)) as (γhm) "Hm".
  { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
  iDestruct "H" as "[H1 H2]".

  iModIntro. iExists (GenHeapG L V Σ _ _ _ _ _ γh γhm). iFrame.
  iExists ∅; simpl. rewrite dom_empty_L. by iSplit.
Qed.

Lemma gen_heap_frag_set `{hG : gen_heapG L V Σ} σ :
  gen_heap_frag σ ⊢ [∗ map] l ↦ v ∈ σ, mapsto l 1 v.
Proof.
  apply (map_ind (λ x, gen_heap_frag x ⊢ [∗ map] l ↦ v ∈ x, mapsto l 1 v)).
  - rewrite big_sepM_empty; auto.
  - intros i w m Hmi Hm.
    rewrite /gen_heap_frag.
    rewrite to_gen_heap_insert.
    rewrite insert_singleton_op; last by apply lookup_to_gen_heap_None.
    rewrite auth_frag_op own_op.
    rewrite big_sepM_insert; last done.
    rewrite {1}mapsto_eq /mapsto_def.
    iIntros "[$ ?]".
    by iApply Hm.
Qed.

Theorem dist_adequacy `{distPreG Σ} IPs A s e σ φ :
  (∀ `{distG Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
                    Fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
                     ([∗ set] ip ∈ IPs, FreeIP ip) -∗ WP e @ s; ⊤ {{v, ⌜φ v⌝ }}) →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ i, i ∈ A → ip_of_address i ∈ IPs) →
  state_heaps σ = ∅ →
  state_sockets σ = ∅ →
  state_ms σ = ∅ →
  @adequate aneris_lang s e σ (λ v _, φ v).
Proof.
  intros Hwp Hipdom Hpiiu Hfixdom Hste Hsce  Hmse;
    eapply (wp_adequacy _ _); iIntros (?); simpl.
  iMod (own_alloc (● (to_agree <$> ∅) : authR system_state_mapUR)) as
      (γmp) "Hmp"; first by rewrite auth_auth_valid fmap_empty.
  iMod (own_alloc (● ∅ ⋅ ◯ ∅: socket_interpR)) as (γsi) "[Hsi Hsi']".
  { apply auth_both_valid; split; done. }
  iMod (own_alloc (to_agree A : agreeR (gsetUR socket_address)))
    as (γsif) "#Hsif"; first done.
  iMod (FreeIps_alloc IPs) as (γips) "[HIPsCtx HIPs]".
  iMod (own_alloc (● (∅: gmap ip_address (gset_disjUR port)))) as (γpiu) "HPiu";
    first by apply auth_auth_valid.
  set (dg :=
         {|
           dist_map_name := γmp;
           dist_si_name := γsi;
           dist_fixed_name := γsif;
           dist_freeips_name := γips;
           dist_freeports_name := γpiu;
         |}).
  iMod (Hwp dg) as (f) "Hwp".
  iAssert (|==>
             ∃ M : gmap socket_address gname,
               (⌜elements (dom (gset socket_address) M) ≡ₚ elements A⌝)
                 ∗ own (A:=socket_interpR) γsi (● (to_agree <$> M)) ∗
                 [∗ map] a ↦ γ ∈ M,
             own (A:=socket_interpR)
                 γsi (◯ {[ a := (to_agree γ) ]}) ∗
                 saved_pred_own (A:=message) γ (f a))%I with
      "[Hsi Hsi']" as "Hsid".
  { pose proof (NoDup_elements A) as Hnd.
    iInduction (elements A) as [|a l] "IHl" forall "Hsi Hsi'".
    - iModIntro. iExists ∅.
      rewrite big_sepM_empty fmap_empty; iFrame.
      iPureIntro. by rewrite dom_empty_L.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "Hsi Hsi'") as (M HMl) "[HM HML]"; iFrame.
      iMod (saved_pred_alloc (f a)) as (γ) "Hγ".
      assert (a ∉ dom (gset _) M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A:=socket_interpR) _ (● (to_agree <$> M))
                       (● (<[a := to_agree γ ]>(to_agree <$> M) :
                             gmapUR socket_address (agreeR (leibnizO gname)))
                          ⋅ (◯ ({[a := to_agree γ]} :
                                  gmapUR socket_address (agreeR (leibnizO gname)
                       )))) with "HM") as "[HM Hγ']".
      { apply auth_update_alloc. rewrite -insert_empty.
        rewrite /ε /= /gmap_unit.
        apply (alloc_local_update
                 (_ : gmapUR socket_address (agreeR (leibnizO gname)))); last done.
        eapply (not_elem_of_dom (D := gset socket_address)).
        by rewrite dom_fmap. }
      iModIntro.
      iExists (<[a:= γ]> M).
      rewrite fmap_insert; iFrame.
      rewrite big_sepM_insert;
        last by apply (not_elem_of_dom (D := gset socket_address)).
      iFrame. iPureIntro.
      rewrite dom_insert_L elements_union_singleton; auto. }
  iMod "Hsid" as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply elem_of_equiv_L => x; split => Hx;
    apply elem_of_elements; apply elem_of_elements in Hx;
    first by rewrite -HMfs. by rewrite HMfs. }
  iIntros (?). iModIntro.
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (@big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iExists
    (λ σ κs,
     (∃ (m : gmap ip_address node_gnames),
         ⌜gnames_coherence m (state_heaps σ) (state_sockets σ)⌝ ∗
          socket_interp_coherence (state_ports_in_use σ) ∗
          ownS dist_map_name m ∗
          ([∗ map] n ↦ γs ∈ m, local_state_interp σ n γs) ∗
          FipPiu σ ∗
          network_coherence (state_sockets σ) (state_ms σ) (state_ports_in_use σ))%I),
  (λ _, True)%I.
  iSplitR "Hwp HIPs"; last first.
  - iApply "Hwp"; iFrame "#"; iFrame.
  - iFrame. iExists _; iFrame. iSplit.
    { iPureIntro. by split; rewrite ?Hste ?Hsce !dom_empty_L. }
    iSplitL "HM".
    { rewrite /socket_interp_coherence. iExists _; iFrame.
      iExists _; iFrame; iFrame "#".
      rewrite -!Hdmsi dom_fmap_L. rewrite -Hdmsi -Hipdom in Hfixdom.
      iSplit; first done.
      iSplit; last by iApply (@big_sepS_mono with "[$Hsa']"); simpl; auto.
      iPureIntro. intros b. split; first by auto.
      intros [Hb | [Hb HP]]; first done.
      rewrite -Hipdom in Hpiiu. specialize (Hpiiu _ H0).
      specialize (HP _ Hpiiu). done. }
    iSplitR.
    { by rewrite big_sepM_empty. }
    iSplitL "HIPsCtx HPiu".
    { iExists _, _; iFrame.
      iPureIntro; repeat split; trivial.
      - by rewrite dom_empty.
      - rewrite Hste. by rewrite lookup_empty.
      - rewrite Hsce. by rewrite lookup_empty.
      - intros ? ?; by rewrite lookup_empty. }
    iSplit. iPureIntro. rewrite Hsce Hmse. repeat split; eauto; try set_solver.
    rewrite /network_messages_coherence.
    rewrite Hmse Hsce. done.
Qed.

Definition safe e σ := @adequate aneris_lang NotStuck e σ (λ _ _, True).

Theorem adequacy `{distPreG Σ} IPs A e σ :
  (∀ `{distG Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
                    Fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
                     ([∗ set] ip ∈ IPs, FreeIP ip) -∗ WP e {{v, True }}) →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ i, i ∈ A → ip_of_address i ∈ IPs) →
  state_heaps σ = ∅ → state_sockets σ = ∅ → state_ms σ = ∅ →
  safe e σ.
Proof.
  intros.
  eapply dist_adequacy; eauto.
Qed.

Theorem adequacy_hoare `{distPreG Σ} IPs A e σ φ :
  (∀ `{distG Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
      {{{ Fixed A ∗ ([∗ set] a ∈ A, a ⤇ (f a)) ∗ ([∗ set] ip ∈ IPs, FreeIP ip) }}}
          e
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ i, i ∈ A → ip_of_address i ∈ IPs) →
  state_heaps σ = ∅ →
  state_sockets σ = ∅ →
  state_ms σ = ∅ →
  @adequate aneris_lang NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp Hipdom Hpiiu Hfixdom Hste Hsce Hmse.
  eapply dist_adequacy; try eauto. intros H'.
  specialize (Hwp H').
  iModIntro. iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros.
  iApply ("Hwp" with "[$]").
  iNext. by iIntros (?) "H".
Qed.

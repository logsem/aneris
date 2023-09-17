From stdpp Require Import option.
From trillium.fairness Require Export fuel utils. 


(* TODO: implement LiveModel with ls_tmap as primitive 
         and define ls_mapping on top of it.
         Previous attempt to do so failed due to weird implicit arguments errors
 *)
Section LsTmap.
  Context `{LM: LiveModel G M LSI}.
  Context `{Countable G}.

  Definition ls_tmap (δ: lm_ls LM): gmap G (gset (fmrole M)).
  Admitted.

  Lemma ls_tmap_fuel_same_doms (δ: lm_ls LM):
      forall ρ, ρ ∈ dom (ls_fuel δ) <-> exists τ R, ls_tmap δ !! τ = Some R /\ ρ ∈ R.
  Proof. Admitted.

  Lemma ls_tmap_disj (δ: lm_ls LM):
    forall (τ1 τ2: G) (S1 S2: gset (fmrole M)) (NEQ: τ1 ≠ τ2),
      ls_tmap δ !! τ1 = Some S1 -> ls_tmap δ !! τ2 = Some S2 -> S1 ## S2.
  Proof. Admitted. 

  Definition ls_mapping_impl (tmap: gmap G (gset (fmrole M))): gmap M.(fmrole) G :=
    let tmap_l := map_to_list tmap in
    let tmap_flat := flat_map (fun '(τ, R) => map (pair τ) (elements R)) tmap_l in
    let tmap_rev := (fun '(τ, ρ) => (ρ, τ)) <$> tmap_flat in
    list_to_map tmap_rev.
    
  Lemma fmap_flat_map {A B C: Type} (f : A → list B) (g: B -> C) (l : list A):
      g <$> (flat_map f l) = flat_map ((fmap g) ∘ f) l.
  Proof.
    induction l; [done| ].
    simpl. rewrite fmap_app. congruence.
  Qed.

  (* TODO: upstream *)
  Lemma concat_NoDup {A: Type} (ll : list (list A)):
    (forall i l, ll !! i = Some l -> NoDup l) ->
    (forall i j li lj, i ≠ j -> ll !! i = Some li -> ll !! j = Some lj -> li ## lj) ->
    NoDup (concat ll).
  Proof.
    induction ll.
    { constructor. }
    intros. simpl. apply NoDup_app. repeat split.
    { apply (H0 0). done. }
    2: { apply IHll.
         - intros. apply (H0 (S i)). done.
         - intros. apply (H1 (S i) (S j)); auto. }
    intros. intros [lx [INlx INx]]%elem_of_list_In%in_concat.
    apply elem_of_list_In, elem_of_list_lookup_1 in INlx as [ix IX].
    eapply (H1 0 (S ix)).
    - lia.
    - simpl. reflexivity.
    - simpl. apply IX.
    - eauto.
    - by apply elem_of_list_In.
  Qed.

  (* Lemma ls_mapping_tmap_corr_impl tmap: *)
  (*   maps_inverse_match (ls_mapping_impl tmap) tmap. *)
  (* Proof. *)
  (* Admitted.  *)

  Lemma ls_mapping_tmap_corr δ:
    maps_inverse_match (ls_mapping δ) (ls_tmap δ).
  Proof.
    (* red. intros. rewrite /ls_mapping. *)
    (* etransitivity. *)
    (* { symmetry. apply elem_of_list_to_map. *)
    (*   rewrite -list_fmap_compose. *)
    (*   rewrite fmap_flat_map. *)
    (*   rewrite flat_map_concat_map. apply concat_NoDup. *)
    (*   { intros. apply list_lookup_fmap_Some in H0 as [[??] [? ->]]. *)
    (*     simpl. rewrite -list_fmap_compose. *)
    (*     apply NoDup_fmap_2; [apply _| ]. *)
    (*     apply NoDup_elements. } *)
    (*   intros. *)
    (*   apply list_lookup_fmap_Some in H1 as [[??] [? ->]]. *)
    (*   apply list_lookup_fmap_Some in H2 as [[??] [? ->]]. *)
    (*   simpl. apply elem_of_disjoint. *)
    (*   intros ? [[??] [-> ?]]%elem_of_list_fmap_2 [[??] [? ?]]%elem_of_list_fmap_2. *)
    (*   simpl in H4. subst. *)
    (*   apply elem_of_list_fmap_2 in H3 as [? [[=] ?]]. *)
    (*   apply elem_of_list_fmap_2 in H5 as [? [[=] ?]]. *)
    (*   subst. *)
    (*   assert (ls_tmap δ !! l = Some g). *)
    (*   { eapply elem_of_map_to_list. eapply elem_of_list_lookup_2; eauto. } *)
    (*   assert (ls_tmap δ !! l0 = Some g0). *)
    (*   { eapply elem_of_map_to_list. eapply elem_of_list_lookup_2; eauto. } *)
    (*   assert (l ≠ l0). *)
    (*   { intros <-. *)
    (*     pose proof (NoDup_fst_map_to_list (ls_tmap δ)). *)
    (*     eapply NoDup_alt in H5. *)
    (*     { apply H0, H5. } *)
    (*     all: apply list_lookup_fmap_Some; eauto. } *)
    (*   pose proof (@ls_tmap_disj δ _ _ _ _ H5 H3 H4). *)
    (*   set_solver. } *)
    (* etransitivity. *)
    (* { apply elem_of_list_fmap. } *)
    (* transitivity ((v, k) *)
    (*    ∈ flat_map (λ '(τ, R), map (pair τ) (elements R)) (map_to_list (ls_tmap δ))). *)
    (* { split. *)
    (*   - intros (?&?&?). destruct x. congruence. *)
    (*   - intros. exists (v, k). eauto. } *)
    (* rewrite elem_of_list_In. *)
    (* rewrite in_flat_map. *)

    (* split. *)
    (* - intros [[??][IN1 IN2]]. *)
    (*   apply elem_of_list_In, elem_of_map_to_list in IN1. *)
    (*   apply in_map_iff in IN2 as [? [[=] yy]]. subst. *)
    (*   eexists. split; eauto. *)
    (*   apply elem_of_list_In in yy. set_solver. *)
    (* - intros [? [??]]. exists (v, x). split. *)
    (*   + by apply elem_of_list_In, elem_of_map_to_list. *)
    (*   + apply in_map_iff. eexists. split; eauto. *)
    (*     apply elem_of_list_In. set_solver. *)
  (* Qed. *)
  Admitted.
      
  
  (* Lemma ls_same_doms δ: dom (ls_mapping δ) = dom (ls_fuel δ). *)
  (* Proof. *)
  (*   pose proof (ls_tmap_same_doms δ). apply set_eq. *)
  (*   intros. split; intros. *)
  (*   - apply H0. apply elem_of_dom in H1 as [? ?]. *)
  (*     apply ls_mapping_tmap_corr in H1. eauto. *)
  (*   - apply H0 in H1 as [? H1]. apply ls_mapping_tmap_corr in H1. *)
  (*     eapply elem_of_dom; eauto. *)
  (* Qed. *)

  Definition build_LS_ext 
    (st: fmstate M) (fuel: gmap (fmrole M) nat)
    (LIVE_FUEL: live_roles _ st ⊆ dom fuel)
    (tmap: gmap G (gset (fmrole M)))
    (TMAP_FUEL_SAME_DOMS: forall ρ, ρ ∈ dom (fuel) <-> exists τ R, tmap !! τ = Some R /\ ρ ∈ R)
    (LS_TMAP_DISJ: forall (τ1 τ2: G) (S1 S2: gset (fmrole M)) (NEQ: τ1 ≠ τ2),
      tmap !! τ1 = Some S1 -> tmap !! τ2 = Some S2 -> S1 ## S2)
    (LS_INV: LSI st (ls_mapping_impl tmap) fuel): 
    LiveState G M LSI.
  Admitted. 

  Lemma build_LS_ext_spec_st st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
    ls_under (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = st.
  Proof. Admitted. 

  Lemma build_LS_ext_spec_fuel st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
    ls_fuel (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = fuel.
  Proof. Admitted. 

  Lemma build_LS_ext_spec_tmap st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
    ls_tmap (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = tmap.
  Proof. Admitted. 

  Lemma build_LS_ext_spec_mapping st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV
        rmap (MATCH: maps_inverse_match rmap tmap):
    ls_mapping (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = rmap. 
  Proof. 
    eapply maps_inverse_match_uniq1.
    - apply ls_mapping_tmap_corr. 
    - by rewrite build_LS_ext_spec_tmap.
  Qed.

End LsTmap.

From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode notation.

Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c".
Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.

(** The CMRA & functor we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)
Class spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitO) }.
Local Existing Instance spawn_tokG.

Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{LM: LiveModel heap_lang M}. 
Context `{!heapGS Σ LM, !spawnG Σ}.
Context `{PMPP: @PartialModelPredicatesPre _ M _ _ Σ iM}.
Context `{PMP: @PartialModelPredicates _ _ LM _ _ _ _ _ iLM PMPP}.

Context (N : namespace).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).

Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l Ψ).

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)

(* (* TODO: generalize, move *) *)
(*     iApply wp_lift_pure_step_no_fork; auto.  *)
(*     2: do 3 iModIntro; iSplitL "FUELS". *)
(*     2: { iApply (has_fuels_gt_1 with "FUELS"). compute_done. } *)
(*     { set_solver. } *)
(*     iIntros "FUELS". *)
(*     simpl. repeat rewrite fmap_insert. rewrite fmap_empty. simpl. *)

     
Close Scope Z_scope. 
Notation "'sub' d" := (fun n => n - d) (at level 10). 

Lemma sub_comp (fs: gmap (fmrole iM) nat) (d1 d2: nat):
  (sub d1 ∘ sub d2) <$> fs = sub (d1 + d2) <$> fs.
Proof.
  apply leibniz_equiv. apply map_fmap_proper; [| done].
  intros ??->. apply leibniz_equiv_iff.
  rewrite /compose. lia. 
Qed.

Lemma sub_0_id (fs: gmap (fmrole iM) nat):
  fs = sub 0 <$> fs.
Proof.
  rewrite -{1}(map_fmap_id fs).
  apply leibniz_equiv. apply map_fmap_proper; [| done].
  intros ??->. apply leibniz_equiv_iff.
  simpl. lia.
Qed.

Ltac solve_fuels_ge_1 FS := 
  intros ?? [? [<- GE]]%lookup_fmap_Some; apply FS in GE; simpl; lia.

Ltac solve_fuels_S FS := 
  iDestruct (has_fuels_gt_1 with "FUELS") as "F";
  [| rewrite -map_fmap_compose; by iFrame];
  solve_fuels_ge_1 FS. 

Ltac pure_step FS :=
  try rewrite sub_comp;
  iApply wp_lift_pure_step_no_fork; auto;
  [| do 3 iModIntro; iSplitL "FUELS"];
  [| solve_fuels_S FS |];
  [by intros ?%fmap_empty_iff| ];
  iIntros "FUELS"; simpl; rewrite sub_comp. 

Definition final_viewshift (ρ: fmrole iM): iProp Σ.
Admitted. 

(* TODO: move to resources.v *)
Lemma fuels_ge_union_l (fs1 fs2: gmap (fmrole iM) nat) b
  (GE: fuels_ge (fs1 ∪ fs2) b) (DISJ: fs1 ##ₘ fs2):
  fuels_ge fs1 b.
Proof. 
  intros ???. eapply GE. erewrite lookup_union_Some_l; eauto. 
Qed.  

(* TODO: move to resources.v *)
Lemma fuels_ge_union_r (fs1 fs2: gmap (fmrole iM) nat) b
  (GE: fuels_ge (fs1 ∪ fs2) b) (DISJ: fs1 ##ₘ fs2):
  fuels_ge fs2 b.
Proof. 
  intros ???. eapply GE. erewrite lookup_union_Some_r; eauto. 
Qed.  

(* TODO: get rid of has_fuels_S *)
Lemma spawn_spec tid (Ψ : val → iProp Σ) (f : val) 
  (ρ_end2: fmrole iM) (f_end2: nat)
  (fs1 fs2 : gmap (fmrole iM) nat)
  (DISJ: fs1 ##ₘ fs2)
  (* (NE: fs1 ∪ fs2 ≠ ∅) *)
  (NE1: fs1 ≠ ∅)
  (FS: fuels_ge (fs1 ∪ fs2) 9)
  (END2: f_end2 >= 1)
  :
  {{{ has_fuels tid (fs1 ∪ fs2) ∗ 
      ▷ (∀ tid', has_fuels tid' (sub 6 <$> fs2) -∗ WP f #() @ tid' {{ v, Ψ v ∗ has_fuels tid' {[ ρ_end2 := f_end2]} }}) ∗
      final_viewshift ρ_end2
  }}} 
    spawn f @ tid
  {{{ l, RET #l; join_handle l Ψ ∗ has_fuels tid (sub 8 <$> fs1)}}}.
Proof.
  iIntros (Φ) "(FUELS & FORK & FIN_VS) HΦ". rewrite /spawn /=.
  assert (fs1 ∪ fs2 ≠ ∅) as NE.
  { (* TODO: why this approach doesn't work? *)
    (* intros E. *)
    (* eapply empty_union_L in E. Unshelve. *)
    admit. }

  rewrite (sub_0_id (_ ∪ _)). 
   
  pure_step FS. 
  pure_step FS. 
 
  (* iDestruct (has_fuels_gt_1 with "FUELS") as "FUELS". *)
  (* { intros ?? [? [<- GE]]%lookup_fmap_Some. simpl. lia. } *)
  wp_bind (Alloc _)%E. iApply (wp_alloc_nostep with "[FUELS]").
  2: { solve_fuels_S FS. }
  { by intros ?%fmap_empty_iff. }
  iNext. iIntros (l) "(L & TKN & FUELS)". rewrite sub_comp.  

  pure_step FS. 
  pure_step FS.

  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.

  (* TODO: why fupd_wp is needed here now? *)
  iApply fupd_wp.  
  iMod (inv_alloc N _ (spawn_inv γ l Ψ) with "[L]") as "#SPAWN_INV".
  { iNext. iExists NONEV. iFrame; eauto. }

  iModIntro.
  wp_bind (Fork _)%E. 

  (* wp_smart_apply (wp_fork with "[Hf]"). *)
  (* - iNext. wp_bind (f _). iApply (wp_wand with "Hf"); iIntros (v) "Hv". *)
  (*   wp_inj. iInv N as (v') "[Hl _]". *)
  (*   wp_store. iSplitL; last done. iIntros "!> !>". iExists (SOMEV v). iFrame. eauto. *)
  (* - wp_pures. iApply "HΦ". rewrite /join_handle. eauto. *)

  iApply (wp_fork_nostep_alt with "[FORK FIN_VS] [HΦ Hγ] [FUELS]").
  5: { iApply has_fuels_proper; [reflexivity| ..]. 
       2: { solve_fuels_S FS. }
       rewrite !map_fmap_union. reflexivity. }
  { by apply map_disjoint_fmap. }
  { rewrite -map_fmap_union. by intros ?%fmap_empty_iff. }
  - iIntros (tid'). iNext. iIntros "FUELS".
    wp_bind (f _). iApply (wp_wand with "[FORK FUELS]").
    { iApply "FORK". by rewrite sub_comp. } 
    iIntros (v) "[Hv FUELS]".

    iAssert (∃ s1 s2, ⌜ fmtrans _ s1 (Some ρ_end2) s2 ⌝∗ 
                      ⌜ ρ_end2 ∉ live_roles _ s2 ⌝ ∗
                      ⌜ live_roles iM s2 ⊆ live_roles iM s1 ⌝ ∗
                      partial_model_is s1)%I with "[FIN_VS]" as (??) "(%STEP&%NL2&%L12&S1)". 
    { (* TODO: use final_viewshift in client invariant  
         such that its ownership implies the existence of such transition *)
      admit. }
    
    
    (* wp_inj. iInv N as (v') "[Hl _]". *)
    (* wp_store. iSplitL; last done. iIntros "!> !>". iExists (SOMEV v). iFrame. eauto. *)
    clear FS. assert (fuels_ge {[ρ_end2 := f_end2]} 1) as FS.
    { red. intros ???%lookup_singleton_Some. lia. }
    assert ({[ρ_end2 := f_end2]} ≠ (∅: gmap (fmrole iM) nat)) as NE'.
    { intros ?.
      (* TODO: ??? *)
      (* set_solver.  *)
      admit. }
    rewrite (sub_0_id {[_ := _]}). 
    wp_bind (InjR _)%E. pure_step FS.   
    iApply wp_value.
    
    iApply wp_atomic. (* TODO: how does that work? *)
    iApply fupd_wp.
    
    iInv N as (v') "[Hl SPAWN]" "CLOSE".
    iApply (wp_store_step_singlerole with "[-CLOSE Hv]"); eauto.
    { apply inj_le, le_0_n. }
    { rewrite map_fmap_singleton has_fuel_fuels. iFrame. }

    do 2 iModIntro. iNext.
    rewrite decide_False; [| done]. iIntros "(?&ST2&ROLES&?)".
    iAssert (⌜ True ⌝)%I with "[ST2]" as "_".
    { (* TODO: here the client invariant should be restored
         by storing the new state *)
      admit. }
    iMod ("CLOSE" with "[-ROLES]") as "_".
    2: { iFrame. done. }
    rewrite /spawn_inv. iNext. iExists _. iFrame.
    iRight. iExists _. iFrame. done.
  - iNext. iIntros "FUELS". iModIntro.
    apply fuels_ge_union_l in FS; [| done].
    pure_step FS.
    pure_step FS.
    iApply wp_value'. iApply "HΦ".
    rewrite /join_handle. iFrame. eauto. 
Admitted. 

Lemma join_spec tid (Ψ : val → iProp Σ) l (fs: gmap (fmrole iM) nat)
  (NE: fs ≠ ∅) (FS: fuels_ge fs 1):
  {{{ join_handle l Ψ ∗ has_fuels tid fs }}} 
    join #l @tid 
  {{{ v, RET v; Ψ v ∗ has_fuels tid (sub 1 <$> fs) }}}.
Proof.
  iIntros (Φ) "[H FUELS] HΦ". iDestruct "H" as (γ) "[Hγ #?]".
  iLöb as "IH".

  (* wp_rec. *)
  rewrite (sub_0_id fs). rewrite /join. pure_step FS. 

  wp_bind (! _)%E.
  (* TODO: why fupd_wp is needed here now? *)
  iApply fupd_wp.  
  iInv N as (v) "[>Hl Hinv]".  

  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iModIntro. iSplitL "Hl"; [iNext; iExists _; iFrame; eauto|].
    wp_smart_apply ("IH" with "Hγ [HΦ]"). auto.
  - iDestruct "Hinv" as (v' ->) "[HΨ|Hγ']".
    + iModIntro. iSplitL "Hl Hγ"; [iNext; iExists _; iFrame; eauto|].
      wp_pures. by iApply "HΦ".
    + iCombine "Hγ Hγ'" gives %[].
Qed.
End proof.

Typeclasses Opaque join_handle.

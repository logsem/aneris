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

Ltac solve_fuels_ge_1 FS := 
  intros ?? [? [<- GE]]%lookup_fmap_Some; apply FS in GE; simpl; lia.

Ltac solve_fuels_S FS := 
  iDestruct (has_fuels_gt_1 with "FUELS") as "F";
  [| rewrite -map_fmap_compose; by iFrame];
  solve_fuels_ge_1 FS. 

Ltac pure_step FS :=
  iApply wp_lift_pure_step_no_fork; auto;
  [| do 3 iModIntro; iSplitL "FUELS"];
  [| solve_fuels_S FS |];
  [by intros ?%fmap_empty_iff| ];
  iIntros "FUELS"; simpl. 
     
Close Scope Z_scope. 
Notation "'sub' d" := (fun n => n - d) (at level 10). 

(* TODO: get rid of has_fuels_S *)
Lemma spawn_spec tid (Ψ : val → iProp Σ) (f : val) 
  (fs1 fs2 : gmap (fmrole iM) nat)
  (DISJ: fs1 ##ₘ fs2)
  (NE: fs1 ∪ fs2 ≠ ∅)
  (FS: fuels_ge (fs1 ∪ fs2) 6)
  :
  {{{ has_fuels tid (fs1 ∪ fs2) ∗ ▷ (has_fuels tid (sub 3 <$> fs2) -∗ WP f #() @ tid {{ Ψ }}) }}} spawn f @ tid {{{ l, RET #l; join_handle l Ψ ∗ has_fuels tid (sub 3 <$> fs1)}}}.
Proof.
  iIntros (Φ) "[FUELS FORK] HΦ". rewrite /spawn /=.

  rewrite -(map_fmap_id (fs1 ∪ fs2)). 
   
  pure_step FS. 
  pure_step FS. 
 
  (* iDestruct (has_fuels_gt_1 with "FUELS") as "FUELS". *)
  (* { intros ?? [? [<- GE]]%lookup_fmap_Some. simpl. lia. } *)
  wp_bind (Alloc _)%E. iApply (wp_alloc_nostep with "[FUELS]").
  2: { solve_fuels_S FS. }
  { by intros ?%fmap_empty_iff. }
  iNext. iIntros (l) "(L & TKN & FUELS)". 

  pure_step FS. 
  pure_step FS.

  
 

  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.

  (* TODO: why fupd_wp is needed here now? *)
  iApply fupd_wp.  
  iMod (inv_alloc N _ (spawn_inv γ l Ψ) with "[L]") as "#?".
  { iNext. iExists NONEV. iFrame; eauto. }

  iModIntro.
  wp_bind (Fork _)%E. 










  wp_smart_apply (wp_fork with "[Hf]").
  - iNext. wp_bind (f _). iApply (wp_wand with "Hf"); iIntros (v) "Hv".
    wp_inj. iInv N as (v') "[Hl _]".
    wp_store. iSplitL; last done. iIntros "!> !>". iExists (SOMEV v). iFrame. eauto.
  - wp_pures. iApply "HΦ". rewrite /join_handle. eauto.
Qed.

Lemma join_spec (Ψ : val → iProp Σ) l :
  {{{ join_handle l Ψ }}} join #l {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "H HΦ". iDestruct "H" as (γ) "[Hγ #?]".
  iLöb as "IH". wp_rec. wp_bind (! _)%E. iInv N as (v) "[Hl Hinv]".
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

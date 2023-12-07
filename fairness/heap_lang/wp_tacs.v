From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import utils.
From iris.bi Require Import bi.
From trillium.fairness.heap_lang Require Export lang proofmode_lsi.

Close Scope Z_scope. 

Notation "'sub' d" := (fun n => n - d) (at level 10).

Lemma sub_comp `{Countable K} (fs: gmap K nat) (d1 d2: nat):
  (sub d1 ∘ sub d2) <$> fs = sub (d1 + d2) <$> fs.
Proof.
  apply leibniz_equiv. apply map_fmap_proper; [| done].
  intros ??->. apply leibniz_equiv_iff.
  rewrite /compose. lia.
Qed.

Lemma sub_0_id `{Countable K} (fs: gmap K nat):
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
  [| rewrite -map_fmap_compose; (try rewrite sub_comp); by iFrame];
  solve_fuels_ge_1 FS.

Ltac solve_map_not_empty := intros ?MM%fmap_empty_iff; try rewrite -insert_empty in MM; try apply insert_non_empty in MM; set_solver.

Ltac pure_step_impl FS indep :=
  try rewrite sub_comp;
  iApply wp_lift_pure_step_no_fork; auto;
  [apply indep| ..];
  [| iSplitR; [done| ]; do 3 iModIntro; iSplitL "FUELS"];
  [| solve_fuels_S FS |];
  [solve_map_not_empty| ];
  iIntros "FUELS"; simpl; try rewrite sub_comp.

Ltac pure_step FS indep :=
  pure_step_impl FS indep. 

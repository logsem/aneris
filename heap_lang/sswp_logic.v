From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From heap_lang Require Export heap_lang_defs. 
From heap_lang Require Import tactics notation.


Section SSWP.
  Set Default Proof Using "Type".

  Context `{hGS: @heap1GS Σ}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}. 

  (* Let eGS := heap_fairnessGS.  *)

  Definition sswp (s : stuckness) E e1 (Φ : expr → iProp Σ) : iProp Σ :=
    match to_val e1 with
    | Some v => |={E}=> (Φ (of_val v))
    | None => ∀ σ1,
        gen_heap_interp σ1.(heap) ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs,
         ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
         gen_heap_interp σ2.(heap) ∗ Φ e2 ∗ ⌜efs = []⌝
    end%I.

  Lemma sswp_wand s e E (Φ Ψ : expr → iProp Σ) :
    (∀ e, Φ e -∗ Ψ e) -∗ sswp s E e Φ -∗ sswp s E e Ψ.
  Proof.
    rewrite /sswp. iIntros "HΦΨ HΦ".
    destruct (to_val e); [by iApply "HΦΨ"|].
    iIntros (?) "H". iMod ("HΦ" with "H") as "[%Hs HΦ]".
    iModIntro. iSplit; [done|]. iIntros (????).
    iDestruct ("HΦ" with "[//]") as "HΦ".
    iMod "HΦ". iIntros "!>!>". iMod "HΦ". iIntros "!>". iMod "HΦ" as "(?&?&?)".
    iIntros "!>". iFrame. by iApply "HΦΨ".
  Qed.

  Lemma sswp_fupd s (E E': coPset) e Φ
    (NVAL: language.to_val e = None):
    (|={E, E'}=> (sswp s E' e (fun k => |={E', E}=> Φ k))) -∗ (sswp s E e Φ).
  Proof using.
    iIntros "WP". rewrite /sswp.
    simpl in *. rewrite NVAL. iIntros (?) "HEAP".
    iMod ("WP" with "[$]") as "WP". iMod "WP" as "[? WP]". iModIntro.
    iFrame. iIntros. iMod ("WP" with "[//]") as "X".
    iModIntro. iNext. iMod "X". iModIntro. iMod "X" as "(X & Y & Z)". iFrame.
    done.
  Qed.

  Lemma sswp_pure_step s E e1 e2 (Φ : Prop) Ψ :
    PureExec Φ 1 e1 e2 → Φ → ▷ Ψ e2 -∗ sswp s E e1 Ψ%I.
  Proof.
    iIntros (Hpe HΦ) "HΨ".
    assert (pure_step e1 e2) as Hps.
    { specialize (Hpe HΦ). by apply nsteps_once_inv in Hpe. }
    rewrite /sswp /=.
    assert (to_val e1 = None) as ->.
    { destruct Hps as [Hred _]. specialize (Hred (Build_state ∅ ∅)).
      by eapply reducible_not_val. }
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; [by set_solver|].
    iSplit.
    { destruct s; [|done]. by destruct Hps as [Hred _]. }
    iIntros (e2' σ2 efs Hstep) "!>!>!>".
    iMod "Hclose". iModIntro. destruct Hps as [_ Hstep'].
    apply Hstep' in Hstep as [-> [-> ->]]. by iFrame.
  Qed.
  
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
  Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
  Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
  Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
  Local Hint Resolve to_of_val : core.
  
  #[global] Instance into_val_val v : IntoVal (Val v) v.
  Proof. done. Qed.
  #[global] Instance as_val_val v : AsVal (Val v).
  Proof. by eexists. Qed.
  
  Lemma wp_allocN_seq s E v n (Φ : expr → iProp Σ) :
    0 < n →
    ▷ (∀ (l:loc), ([∗ list] i ∈ seq 0 (Z.to_nat n),
                    (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) -∗ Φ #l) -∗
      sswp s E (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Φ.
  Proof.
    iIntros (HnO) "HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ")
      as "(Hσ & Hl & Hm)".
    { apply heap_array_map_disjoint.
      rewrite length_replicate Z2Nat.id ?Hexend; auto with lia. }
    iFrame.
    iModIntro.
    iSplit; [|done].
    iApply "HΦ".
    iApply big_sepL_sep. iSplitL "Hl".
    + by iApply heap_array_to_seq_pointsto. 
    + iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
  Qed.
  
  Lemma wp_alloc s E v (Φ : expr → iProp Σ) :
    ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ Φ (LitV (LitLoc l))) -∗
      sswp s E (Alloc v) Φ.
  Proof.
    iIntros "HΦ". iApply wp_allocN_seq; [lia|].
    iIntros "!>" (l) "[[Hl Hm] _]". rewrite loc_add_0.
    iApply ("HΦ" with "Hl Hm").
  Qed.
  
  Lemma wp_free s E l v (Φ : expr → iProp Σ) :
    ▷ l ↦ v -∗
    ▷ Φ (Val $ LitV $ LitUnit) -∗
      sswp s E (Free (Val $ LitV $ LitLoc l)) Φ.
  Proof.
    iIntros ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step. by iFrame.
  Qed.
  
  Lemma wp_choose_nat s E (Φ : expr → iProp Σ) :
    ▷ (∀ (n:nat), Φ $ Val $ LitV (LitInt n)) -∗
      sswp s E ChooseNat Φ.
  Proof.
    iIntros "HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iFrame.
    iModIntro.
    iSplit; [|done].
    iApply "HΦ".
    Unshelve. all: apply O.
  Qed.
  
  Lemma wp_load s E l q v (Φ : expr → iProp Σ) :
    ▷ l ↦{q} v -∗
      ▷ (l ↦{q} v -∗ Φ v) -∗
      sswp s E (Load (Val $ LitV $ LitLoc l)) Φ.
  Proof.
    iIntros ">Hl HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (@gen_heap_valid with "Hσ Hl") as %Hheap.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iFrame.
    iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.
  
  Lemma wp_store s E l v' v (Φ : expr → iProp Σ) :
    ▷ l ↦ v' -∗
      ▷ (l ↦ v -∗ Φ $ LitV LitUnit) -∗
      sswp s E (Store (Val $ LitV (LitLoc l)) (Val v)) Φ.
  Proof.
    iIntros ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step. iFrame. iModIntro. iSplit; [|done]. by iApply "HΦ".
  Qed.
  
  Lemma wp_cmpxchg_fail s E l q v' v1 v2 (Φ : expr → iProp Σ) :
    v' ≠ v1 → vals_compare_safe v' v1 →
    ▷ l ↦{q} v' -∗
      ▷ (l ↦{q} v' -∗ Φ $ PairV v' (LitV $ LitBool false)) -∗
      sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ.
  Proof.
    iIntros (??) ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step.
    rewrite bool_decide_false //. iFrame. iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.
  
  Lemma wp_cmpxchg_suc s E l v' v1 v2 (Φ : expr → iProp Σ) :
      v' = v1 → vals_compare_safe v' v1 →
      ▷ l ↦ v' -∗
      ▷ (l ↦ v2 -∗ Φ $ PairV v' (LitV $ LitBool true)) -∗
      sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ.
  Proof.
    iIntros (??) ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iMod "Hclose".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step.
    rewrite bool_decide_true //. iFrame. iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.
    
  Lemma wp_faa s E (l: loc) (i a: Z) (Φ : expr → iProp Σ) :
    ▷ l ↦ #i -∗
    ▷ (l ↦ #(i + a) -∗ Φ #i) -∗
    sswp s E (FAA #l #a) Φ. 
  Proof.
    iIntros ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    rewrite heap_lang_defs.pointsto_unseal. iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iMod "Hclose".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step.
    iFrame. iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.

End SSWP.

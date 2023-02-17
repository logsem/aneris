From iris.algebra Require Import auth excl csum gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import network resources proofmode adequacy.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_proof lock_proof vector_clock_proof.
From aneris.examples.gcounter_convergence Require Import crdt_code crdt_model crdt_resources crdt_proof.

Definition run_prog gcdata (j : nat) (prog : val) (v : val) : expr :=
  Start
    (ip_of_address (gcd_addr_list gcdata !!! j))
    (let: "qi" :=
        gcounter_install (StringOfZ j) v #j
     in prog (Fst "qi") (Snd "qi")).

Definition runner gcdata i (progs : list val) (v : val) : expr :=
  fold_right
    (λ e e', e;; e')%E #()
    ((λ j, run_prog gcdata j (progs !!! (j - i)) v) <$> (seq i (length progs))).

Lemma runner_cons gcdata i prog progs v :
  runner gcdata i (prog :: progs) v = (run_prog gcdata i prog v;; runner gcdata (S i) progs v)%E.
Proof.
  rewrite /runner /=.
  rewrite Nat.sub_diag /=.
  erewrite Forall_fmap_ext_1; first done.
  apply Forall_seq.
  intros j Hj.
  destruct j; first lia.
  replace (S j - i) with (S (j - i)) by lia.
  done.
Qed.

Section runner_spec_helper.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterG Σ gcdata}.

  Definition prog_spec i a ports A (B : gset socket_address)
             (f : socket_address → socket_interp Σ) (prog : val) : iProp Σ :=
    ⌜port_of_address a ∉ ports⌝ ∧
    ∀ GCounter query incr,
      GCounter i 0 -∗
      query_spec GCounter query i a -∗
      incr_spec GCounter incr i a -∗
      free_ports (ip_of_address a) ports -∗
      ([∗ set] a ∈ A, a ⤇ f a) -∗
      ([∗ set] b ∈ B, b ⤳ (∅, ∅)) -∗
      WP prog query incr @[ip_of_address a] {{_, True}}.

  Notation ith_sa i := (gcd_addr_list gcdata !!! i).

  Lemma runner_spec_helper
        k (A Aprogs : gset socket_address)
        (portssocks : list ((gset port) * (gset socket_address)))
        (f : socket_address → socket_interp Σ)
        (progs : list val) v :
    k + length progs ≤ GClen gcdata →
    is_list (gcd_addr_list gcdata) v →
    (∀ a, a ∈ (gcd_addr_list gcdata) → a ∈ A) →
    Aprogs ⊆ A →
    Global_Inv -∗
    ([∗ list] i ∈ seq k (length progs), GCunallocated i) -∗
    ([∗ list] i ↦ a ∈ gcd_addr_list gcdata, a ⤇ GCounter_socket_proto) -∗
    ([∗ set] a ∈ Aprogs, a ⤇ f a) -∗
    ([∗ list] i ∈ seq k (length progs), free_ip (ip_of_address (ith_sa i))) -∗
    ([∗ list] i ∈ seq k (length progs), sendevs_frag i []) -∗
    ([∗ list] i ∈ seq k (length progs), recevs_frag i []) -∗
    ([∗ list] i ↦ prtsas; prog ∈ portssocks; progs,
       ([∗ set] b ∈ prtsas.2, b ⤳ (∅, ∅)) ∗
       prog_spec (k + i) (ith_sa (k + i)) prtsas.1 Aprogs prtsas.2 f prog) -∗
    WP runner gcdata k progs v @["system"] {{ v, ⌜v = #()⌝ }}.
  Proof.
    iIntros (Hprgslen Hv HA HAprogs)
      "#Hinv Huas #Hprotos #HAprogs Hfips Hsevs Hrevs Hprogs".
    iInduction progs as [|prog progs IHprogs] "IH" forall (k Hprgslen portssocks).
    { rewrite /runner /=. iApply aneris_wp_value; done. }
    rewrite runner_cons /run_prog /=.
    destruct (lookup_lt_is_Some_2 (gcd_addr_list gcdata) k) as [sa Hsa];
      first by simpl in *; lia.
    erewrite list_lookup_total_correct; last by eauto.
    iDestruct (big_sepL2_cons_inv_r with "Hprogs") as (ports portss' ->) "[[Hprgsas Hprog] Hprogs]".
    wp_apply (aneris_wp_start (ports.1 ∪ {[port_of_address sa]}));
      first by eapply gcd_addr_list_nonSys; eauto.
    iDestruct "Hfips" as "[$ Hfips]".
    iDestruct "Huas" as "[Hua Huas]".
    iDestruct "Hsevs" as "[Hsev Hsevs]".
    iDestruct "Hrevs" as "[Hrev Hrevs]".
    iSplitR "Hua Hsev Hrev Hprog Hprgsas".
    { iNext. wp_pures. iApply ("IH" with "[] Huas Hfips Hsevs Hrevs [Hprogs]").
      - simpl in *; iPureIntro; lia.
      - iApply (big_sepL2_impl with "Hprogs").
        iIntros "!#" (? ? ? ? ?) "?".
        rewrite Nat.add_succ_comm; done. }
    rewrite Nat.add_0_r.
    iNext.
    iIntros "Hfps".
    erewrite list_lookup_total_correct; last by eauto.
    iDestruct "Hprog" as "[% Hprog]".
    rewrite free_ports_split; last by apply disjoint_singleton_r.
    iDestruct "Hfps" as "[Hfps Hfsa]".
    wp_apply (install_proof with "[$Hua $Hfsa $Hsev $Hrev]");
      [done|done|by iFrame "#"|].
    iIntros (GCounter query incr) "(HG0 & Hq & Hi)".
    wp_pures.
    iApply ("Hprog" with "HG0 Hq Hi Hfps HAprogs Hprgsas").
  Qed.

End runner_spec_helper.

Section runner_spec.
  Context `{!anerisG (GCounterM gcdata) Σ, !GCounterPreG Σ gcdata}.

  Notation ith_sa i := (gcd_addr_list gcdata !!! i).

  Lemma helper_1 k Aprogs f portssocks progs :
    (∀ i j PB PB', portssocks !! i = Some PB → portssocks !! j = Some PB' → PB.2 ## PB'.2) →
    ([∗ list] i↦prtsas;prog ∈ portssocks;progs,
      prog_spec (k + i) (ith_sa (k + i)) prtsas.1 Aprogs prtsas.2 f prog) -∗
    ([∗ set] x ∈ (⋃ portssocks.*2), x ⤳ (∅, ∅)) -∗
    [∗ list] i↦prtsas;prog ∈ portssocks;progs,
      ([∗ set] b ∈ prtsas.2, b ⤳ (∅, ∅)) ∗
      prog_spec (k + i) (ith_sa (k + i)) prtsas.1 Aprogs prtsas.2 f prog.
  Proof.
    iIntros (Hportssocks) "Hprogs Hsocks".
    iInduction portssocks as [|prtskt] "IH" forall (k progs Hportssocks).
    { iDestruct (big_sepL2_nil_inv_l with "Hprogs") as %->; done. }
    iDestruct (big_sepL2_cons_inv_l with "Hprogs") as (? ? ->) "[$ Hprogs]"; simpl.
    iDestruct (big_sepS_union with "Hsocks") as "[$ Hsocks]".
    { apply elem_of_disjoint; intros sa.
      rewrite elem_of_union_list.
      intros Hsa1 [? [(PB & -> & HPB)%elem_of_list_fmap_2 Hsa2]].
      apply elem_of_list_lookup in HPB as [j Hj].
      eapply (Hportssocks 0 (S j)); eauto. }
    setoid_rewrite <- plus_Snm_nSm.
    iApply ("IH" with "[] Hprogs Hsocks"); auto.
    iPureIntro.
    intros i j; apply (Hportssocks (S i) (S j)).
  Qed.

  Lemma helper_2 k :
    ([∗ list] a ∈ gcd_addr_list gcdata, free_ip (ip_of_address a)) -∗
    [∗ list] i ∈ seq k (GClen gcdata), free_ip (ip_of_address (ith_sa (i - k))).
  Proof.
    generalize (gcd_addr_list gcdata); intros l.
    iIntros "Hl".
    iInduction l as [|a l] "IH" forall (k); simpl; first done.
    rewrite Nat.sub_diag /=.
    iDestruct "Hl" as "[$ Hl]".
    iSpecialize ("IH" with "Hl").
    iApply (big_sepL_impl with "IH").
    iIntros "!#" (i ? [-> ?]%lookup_seq).
    replace (S k + i - k) with (S (S k + i - S k)) by lia.
    iIntros "$".
  Qed.

  Lemma helper_3 :
    ([∗ list] a ∈ gcd_addr_list gcdata, free_ip (ip_of_address a)) -∗
    [∗ list] i ∈ seq 0 (GClen gcdata), free_ip (ip_of_address (ith_sa i)).
  Proof.
    iIntros "H".
    iDestruct (helper_2 0 with "H") as "H".
    setoid_rewrite Nat.sub_0_r; done.
  Qed.

  Lemma runner_spec (Aprogs : gset socket_address)
        (portssocks : list ((gset port) * (gset socket_address)))
        (progs : list val) v :
    0 < length progs →
    length progs = GClen gcdata →
    is_list (gcd_addr_list gcdata) v →
    (∀ a, a ∈ (gcd_addr_list gcdata) → a ∉ Aprogs) →
    (list_to_set (gcd_addr_list gcdata) ## (⋃ portssocks.*2)) →
    (∀ i j PB PB', portssocks !! i = Some PB → portssocks !! j = Some PB' → PB.2 ## PB'.2) →
    (|={⊤}=> ∃ f,
       ([∗ list] i ↦ prtsas; prog ∈ portssocks; progs,
       prog_spec i (ith_sa i) prtsas.1 Aprogs prtsas.2 f prog)) -∗
    |={⊤}=> ∃ _ : GCounterG Σ gcdata,
         frag_st (initial_crdt_state (GClen gcdata)) -∗
         unallocated (list_to_set (gcd_addr_list gcdata) ∪ Aprogs) -∗
         ([∗ set] a ∈ list_to_set (C := gset _) (gcd_addr_list gcdata) ∪ (⋃ portssocks.*2),
            a ⤳[bool_decide (a ∈ list_to_set (C := gset _) (gcd_addr_list gcdata)),
                bool_decide (a ∈ list_to_set (C := gset _) (gcd_addr_list gcdata))] (∅, ∅)) -∗
         ([∗ list] a ∈ gcd_addr_list gcdata, sendon_evs a []) -∗
         ([∗ list] a ∈ gcd_addr_list gcdata, receiveon_evs a []) -∗
         ([∗ list] a ∈ gcd_addr_list gcdata, free_ip (ip_of_address a)) -∗
         ([∗ list] i ∈ seq 0 (GClen gcdata), alloc_evs (StringOfZ (i : nat)) []) ={⊤}=∗
         Global_Inv ∗ WP runner gcdata 0 progs v @["system"] {{ v, ⌜v = #()⌝ }}.
  Proof.
    iIntros (Hprogsne Hproglen Hilv HAprogs Hsocks1 Hsocks2) "Hprogs".
    iMod "Hprogs" as (f) "Hprogs".
    iMod Gcounter_init as (γvcs) "Hvcs".
    iMod locations_init as (γlocs) "[Hlocs Hlocsf]".
    iMod (sendevs_init (GClen gcdata)) as (γsendevs) "[Hsevss Hsevssf]".
    iMod (recevs_init (GClen gcdata)) as (γrecevs) "[Hrevss Hrevssf]".
    iModIntro.
    pose ({| GCG_vcs_name := γvcs;
                GCG_locs_name := γlocs;
                GCG_sendevs_name := γsendevs;
                GCG_recevs_name := γrecevs |}).
    iExists _.
    iIntros "Hfst Hfx Hmsgpts Hpsevs Hprevs Hfips Halevs".
    iDestruct (big_sepS_union with "Hmsgpts") as "[Hmsgptscrdt Hmsgptsprogs]"; first done.
    iAssert (|={⊤}=> Global_Inv)%I
      with "[Hvcs Hlocs Hsevss Hrevss Hfst Hpsevs Hprevs Halevs Hmsgptscrdt]" as ">#Hinv".
    { iApply inv_alloc.
      iNext.
      iExists _, _, _, _; iFrame "Hfst Hvcs Hlocs Hsevss Hrevss".
      iDestruct (locations_coh_init with "Halevs") as "$".
      iDestruct (sendevs_coh_init with "Hpsevs") as "$".
      iDestruct (recevs_coh_init with "Hprevs") as "$".
      rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup.
      iApply (big_sepL_impl with "Hmsgptscrdt").
      iIntros "!#" (? ? ?) "H".
      rewrite bool_decide_eq_true_2;
        last by eapply elem_of_list_to_set, elem_of_list_lookup_2; eauto.
      iExists _, _; iFrame; done. }
    iModIntro.
    iSplit; first iFrame "Hinv".
    iDestruct (big_sepS_impl with "Hmsgptsprogs []") as "Hmsgptsprogs".
    { iIntros "!#" (? ?) "H".
      rewrite bool_decide_eq_false_2; last set_solver.
      iExact "H". }
    iDestruct (unallocated_split with "Hfx") as "[Hfx HfxA]"; [set_solver|].
    iApply (aneris_wp_socket_interp_alloc GCounter_socket_proto with "Hfx").
    { destruct progs; [|done]. simpl in *. lia. }
    iIntros "#Hsi".
    iApply (aneris_wp_socket_interp_alloc_fun f with "HfxA").
    { destruct progs; [|done]. simpl in *. lia. }
    iIntros "#HsiA".
    (* TODO: introduce new lemma for allocating socket interps with map *)
    wp_apply (runner_spec_helper 0 (list_to_set (gcd_addr_list gcdata) ∪ Aprogs)
                                 Aprogs portssocks f
                with "Hinv [Hlocsf] [] [] [Hfips] [Hsevssf] [Hrevssf]"); simpl.
    - lia.
    - done.
    - set_solver.
    - set_solver.
    - rewrite Hproglen; done.
    - rewrite big_sepS_list_to_set; last apply gcd_addr_list_NoDup.
      done.
    - done.
    - rewrite Hproglen.
      iApply helper_3; done.
    - rewrite Hproglen; done.
    - rewrite Hproglen; done.
    - iApply (helper_1 0 with "Hprogs Hmsgptsprogs"); done.
Qed.

End runner_spec.

(* TODO : explain the fields *)

Record programs_using_gcounters {gcdata : GCData} :=
  { Aprogs : gset socket_address;
    portssocks : list ((gset port) * (gset socket_address));
    progs : list val;
    progs_ne : 0 < length progs;
    progs_length : length progs = GClen gcdata;
    Aprogs_no_conflict : ∀ a, a ∈ (gcd_addr_list gcdata) → a ∉ Aprogs;
    Aprogs_on_nodes :
      ∀ a, a ∈ Aprogs → ∃ sa, sa ∈ (gcd_addr_list gcdata) ∧ ip_of_address a = ip_of_address sa;
    Aprogs_portssocks_eq : Aprogs = (⋃ portssocks.*2);
    sockets_no_conflict : list_to_set (gcd_addr_list gcdata) ## (⋃ portssocks.*2);
    sockets_disj :
      ∀ i j PB PB', portssocks !! i = Some PB → portssocks !! j = Some PB' → PB.2 ## PB'.2;
    progs_Σ : gFunctors;
    progs_wp :
      (∀ Σ, ∀ `{!anerisG (GCounterM gcdata) Σ, !subG progs_Σ Σ},
          ⊢@{iPropI Σ} |={⊤}=> ∃ f,
       ([∗ list] i ↦ prtsas; prog ∈ portssocks; progs,
       prog_spec i (gcd_addr_list gcdata !!! i) prtsas.1 Aprogs prtsas.2 f prog));
  }.

Arguments programs_using_gcounters _ : clear implicits.

Definition init_state := {|
  state_heaps :=  {["system" := ∅ ]};
  state_sockets := {["system" := ∅ ]};
  state_ms := ∅; |}.

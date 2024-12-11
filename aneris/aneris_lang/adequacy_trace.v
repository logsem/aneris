From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Import language.
From trillium Require Import finitary.
From aneris.aneris_lang.program_logic Require Import aneris_adequacy.
From aneris.aneris_lang Require Import adequacy aneris_lang proofmode adequacy_no_model.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.

Definition aneris_invariance `{anerisPreG Σ unit_model} (N : namespace) (I : list val → Prop) (φ : val → Prop)
  ip e σ A IPs lbls obs_send_sas obs_rec_sas : 
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  state_trace σ = [] →
  ip ∉ IPs →
  obs_send_sas ⊆ A →
  obs_rec_sas ⊆ A →
  I (state_trace σ) →
  (∀ `(anerisG Σ), ⊢ 
    {{{ trace_inv N I ∗
        trace_is (state_trace σ) ∗
        unallocated A ∗
        ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
        ([∗ set] ip ∈ IPs, free_ip ip) ∗
        ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
        ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
        ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
        observed_send obs_send_sas ∗
        observed_receive obs_rec_sas }}} 
    e @[ip]
    {{{ v, RET v; ⌜φ v⌝ }}}) →
  (∀ σ' t,
    rtc step ([(mkExpr ip e)], σ) (t, σ') →
    I (state_trace σ')) ∧
    aneris_adequate e ip σ φ.
Proof.
  intros Hheaps Hsock Hms Htrace Hip_nin Hobs_send Hobs_rec HI Hwp.
  assert ((@continued_simulation aneris_lang (aneris_to_trace_model unit_model)
            (λ ex _, ∀ conf, trace_ends_in ex conf → I (state_trace conf.2))
            (trace_singleton ([(mkExpr ip e)], σ))
            (trace_singleton ())) ∧ 
            aneris_adequate e ip σ φ) as (Hsim & Haneris_adequate).
  {
    eapply (simulation_adequacy Σ (aneris_to_trace_model unit_model) 
              NotStuck IPs lbls A obs_send_sas obs_rec_sas); try done.
    - intros ?.
      intros.
      eapply finite_smaller_card_nat.
      eapply (in_list_finite [((),())]).
      intros state_label _.
      destruct state_label as [u1 u2].
      destruct u1, u2.
      set_solver.
      Unshelve.
      intros.
      apply make_proof_irrel.
    - iIntros.
      iModIntro.
      iExists (λ v, (∃ w : val, ⌜v = {| val_n := ip; val_e := w |}⌝ ∗ ⌜φ w⌝)%I).
      iIntros "Hunalloc Hobs Hfree_ip His_node Hlbs Hsend_evs Hrec_evs 
        Hobs_send Hobs_rec ? Hfrag_trace Htrace_is".
      iMod (inv_alloc N _ (∃ t, trace_half_frag t ∗ ⌜I t⌝)%I with "[Hfrag_trace]") as "#Hinv".
      {
        iNext.
        iExists [].
        iFrame.
        iPureIntro.
        by rewrite -Htrace.
      }
      iModIntro.
      iSplitR; first set_solver.
      iSplitL.
      + 
        unfold aneris_wp_def in Hwp.
        iAssert (WP e @[ip] {{ v, ⌜φ v⌝}}%I) with "[Hunalloc Hobs Hfree_ip 
          Hlbs Hsend_evs Hrec_evs Hobs_send Hobs_rec Htrace_is]" as "Hwp".
        {
          iApply (Hwp anerisG0 with "[$Hinv Htrace_is $Hunalloc Hobs $Hfree_ip 
            $Hlbs $Hsend_evs $Hrec_evs $Hobs_send $Hobs_rec][]"); try done.
          rewrite Htrace.
          iFrame.
          set_solver.
        }
        rewrite !aneris_wp_unfold /aneris_wp_def.
        iApply ("Hwp" with "[$His_node]").
      + iIntros (?????????) "Hinterp ?".
        simpl.
        iInv "Hinv" as ">Hinv_res" "_".
        iDestruct "Hinterp" as "(?&?&?&?&?& Hauth_trace)".
        iApply fupd_mask_intro; first set_solver.
        iIntros.
        unfold trace_auth.
        iDestruct "Hinv_res" as (t') "(Hinv_res1 & %Hinv_res2)".
        iDestruct (trace_auth_half_frag_agree with "Hauth_trace Hinv_res1 ") as %<-.
        iPureIntro.
        intros.
        apply last_eq_trace_ends_in in H6.
        by rewrite H6 in Hinv_res2.
  }
  split; last done.
  intros σ' t Hsteps.
  eapply (@trace_steps_rtc_bin _ unit) in Hsteps; last done.
  destruct Hsteps as [ex (Htrace_steps & Htrace_start & Htrace_end)].
  assert (∃ ex', trace_steps language.locale_step ex' ∧ 
                 trace_starts_in ex' ([{| expr_n := ip; expr_e := e |}], σ) ∧
                 trace_ends_in ex' (t, σ')) 
                 as [ex' (Htrace_steps' & Htrace_start' & Htrace_end')].
  {
    clear Hwp Hsim Hheaps Hsock Hms Htrace HI.
    generalize dependent t.
    generalize dependent σ.
    generalize dependent σ'.
    induction Htrace_steps.
    - intros.
      exists {tr[ x ]}.
      by split; first apply trace_steps_singleton.
    - intros.
      apply trace_extend_starts_in_inv in Htrace_start.
      destruct x.
      eapply IHHtrace_steps in Htrace_start; last apply H0; last done.
      destruct Htrace_start as 
        [ex' (Htrace_steps' & Htrace_start' & Htrace_end')].
      inversion H1.
      + exists (ex' :tr[ (Some $ locale_of t1 e1) ]: y).
        split.
        * apply (trace_steps_step _ _ (l, s)); try done.
          simplify_eq.
          eapply locale_step_atomic; done.
        * split; last done. 
          by apply trace_extend_starts_in.
      + exists (ex' :tr[ None ]: y).
        split.
        * apply (trace_steps_step _ _ (l, s)); try done.
          simplify_eq.
          eapply locale_step_state; done.
        * split; last done. 
          by apply trace_extend_starts_in.
  }
  assert (∃ atr, trace_starts_in atr () ∧ 
                 continued_simulation 
                 (λ (ex : execution_trace aneris_lang) 
                    (_ : auxiliary_trace (aneris_to_trace_model unit_model)), 
                     ∀ conf : cfg aneris_lang, trace_ends_in ex conf → 
                                               I (state_trace conf.2)) 
                  ex' atr) as [atr (_ & Hsim_ex')].
  {
    eapply (@simulation_does_continue 
                        aneris_lang 
                        (aneris_to_trace_model unit_model)); try done.
  }
  apply continued_simulation_rel in Hsim_ex'.
  by apply Hsim_ex' in Htrace_end'.
Qed.

Theorem adequacy_trace_with_aneris_adequacy Σ `{anerisPreG Σ unit_model} {L : Type} (N : namespace) ip
  (Φ : ∀ `{anerisG Σ}, L → iProp Σ) (φ : val → Prop)
  (e : expr) (lib : L) (valid_trace: list val → Prop) 
  (σ: state) (A : gset socket_address) (IPs : gset ip_address)  :
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  state_trace σ = [] →
  ip ∉ IPs →
  valid_trace [] →
  (∀ `{anerisG Σ}, ⊢ (trace_is [] ∗ trace_inv N valid_trace) ={⊤}=∗ Φ lib) →
  (∀ `{anerisG Σ}, ⊢ 
    {{{ Φ lib ∗ unallocated A ∗ ([∗ set] a ∈ A, a ⤳ (∅, ∅)) ∗ ([∗ set] ip ∈ IPs, free_ip ip) }}} 
    e @[ip] 
    {{{ v, RET v; ⌜φ v⌝ }}}) →
  (∀ σ' e',
    rtc step ([(mkExpr ip e)], σ) (e', σ') →
    valid_trace (state_trace σ')) ∧
    aneris_adequate e ip σ φ.
Proof.
  intros Hstate_heap Hstate_sock Hstate_ms Hstate_trace Hips_nin.
  intros Htr Hinit Hclient.
  rewrite -Hstate_trace in Htr.
  eapply (aneris_invariance _ _ _ _ _ _ A _ ∅ ∅ ∅); try done.
  iIntros (? ?) "!# (#HI & Htr & Hunalloc & Hobs & Hfree_ip & Hlbs 
    & Hsend_evs & Hrec_evs & Hobs_send & Hobs_rec) HΦ".
  iApply fupd_aneris_wp.
  rewrite Hstate_trace.
  iMod (Hinit with "[$Htr $HI]") as "Hinit'".
  iModIntro.
  iApply (Hclient with "[$Hunalloc $Hfree_ip $Hobs $Hinit'][HΦ]"); last done.
Qed.

Theorem adequacy_trace Σ `{anerisPreG Σ unit_model} {L : Type} (N : namespace) ip
  (Φ : ∀ `{anerisG Σ}, L → iProp Σ) 
  (e : expr) (lib : L) (valid_trace: list val → Prop) 
  (σ: state) (A : gset socket_address) (IPs : gset ip_address)  :
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  state_trace σ = [] →
  ip ∉ IPs →
  valid_trace [] →
  (∀ `{anerisG Σ}, ⊢ (trace_is [] ∗ trace_inv N valid_trace) ={⊤}=∗ Φ lib) →
  (∀ `{anerisG Σ}, ⊢ 
    {{{ Φ lib ∗ unallocated A ∗ ([∗ set] a ∈ A, a ⤳ (∅, ∅)) ∗ ([∗ set] ip ∈ IPs, free_ip ip) }}} 
    e @[ip] 
    {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc step ([(mkExpr ip e)], σ) (e', σ') →
    valid_trace (state_trace σ').
Proof.
  intros Hstate_heap Hstate_sock Hstate_ms Hstate_trace Hips_nin.
  intros Htr Hinit Hclient.
  eapply (adequacy_trace_with_aneris_adequacy _ _ ip _ (λ _, True)); try done.
Qed.
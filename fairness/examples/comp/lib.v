From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness Require Import lm_fair fuel_ext.
From trillium.fairness.heap_lang Require Import notation.

Close Scope Z_scope.

Section LibraryDefs.

  Definition lib_model_impl: FairModel.
    refine ({|
        fmstate := nat;
        fmrole := unit;
        fmtrans s1 oρ s2 := s1 = 1 /\ s2 = 0;
        live_roles s := if (decide (s = 1)) then {[ tt ]} else ∅;
        (* fuel_limit _ := 25%nat; (* exact value; should relax its usage *) *)
             |}).
    intros. set_solver. 
  Defined. 

  (* simply to differentiate between group- and individual role *)
  Definition lib_grole := unit.
  Definition ρlg: lib_grole := tt. 

  Definition ρl: fmrole lib_model_impl := tt.

  Definition lib_model: LiveModel lib_grole lib_model_impl LSI_True := 
    {| lm_fl _ := 5; |}.  
  
  Definition lib_fun: val.
  Admitted.

  Lemma lib_model_impl_lr_strong: FM_strong_lr lib_model_impl.
  Proof. 
    red. intros. simpl.
    destruct st; [| destruct st]; set_solver. 
  Qed. 

  (* TODO: this is needed to prove lib termination; should extract this part *)
  From trillium.fairness Require Import fair_termination trace_helpers trace_lookup. 

  (* straightforward proof which can be done more idiomatically 
     by providing FairTerminatingModel of library *)
  Lemma lib_fair_term:
    ∀ mtr: mtrace lib_model_impl, mtrace_fairly_terminating mtr. 
  Proof.
    red. intros mtr VALID FAIR. 
    destruct mtr; [by exists 1| ].
    destruct mtr; [by exists 2| ].
    pose proof (trace_valid_steps' _ _ VALID 0) as STEP0.
    pose proof (trace_valid_steps' _ _ VALID 1) as STEP1.
    rewrite trace_lookup_0_cons in STEP0. simpl in STEP0. 
    specialize (STEP0 _ _ _ eq_refl) as [-> ->].
    rewrite trace_lookup_cons trace_lookup_0_cons in STEP1.
    specialize (STEP1 _ _ _ eq_refl). by inversion STEP1.
  Qed.


  (* TODO: generalize to any LSI_True model *)
  Instance lib_model_inh: Inhabited (lm_ls lib_model).
  Proof. 
    pose proof (fmrole_inhabited lib_model_impl) as [ρ].
    pose proof (fmstate_inhabited lib_model_impl) as [s].
    eapply populate, (initial_ls s ρ). done.
  Qed.

  Global Instance lib_LF: LMFairPre lib_model.
    esplit; by apply _.
  Defined.
  
  Definition lib_fair := LM_Fair (LM := lib_model). 

End LibraryDefs.

Global Opaque lib_model_impl. 
Global Opaque lib_grole ρlg. 

Section LibrarySpec.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ lib_model_impl}.
  (* Context {ifG: fairnessGS lib_model Σ}. *)
  
  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := lib_model) (PMPP := PMPP) (eGS := heap_fairnessGS))).

  Lemma lib_spec tid Einvs:
    PMP Einvs -∗
    {{{ partial_model_is 1 (PartialModelPredicatesPre := PMPP) ∗ 
        has_fuels tid {[ ρl:=2 ]} (PMPP := PMPP)  }}}
      lib_fun #() @ tid
    {{{ RET #(); partial_mapping_is {[ tid := ∅ ]} ∗ 
                 partial_free_roles_are {[ ρl ]} }}}.
  Proof using. Admitted.

End LibrarySpec.

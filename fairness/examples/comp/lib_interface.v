From iris.bi Require Import bi.
From trillium.fairness.heap_lang Require Import lang.
From trillium.fairness Require Import fairness.
From trillium.fairness.ext_models Require Import ext_models.
From trillium.program_logic Require Import ewp. 
From trillium.fairness.heap_lang Require Import heap_lang_defs lang notation.

Section LibInterface.

  Definition in_dom_rel {A: Type} (R: relation A) :=
    fun x => exists y, R x y. 

  Definition in_cod_rel {A: Type} (R: relation A) :=
    fun y => exists x, R x y. 

  Let PI
    (* `{hG: gen_heapGS loc val Σ} *)
    `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}
    (p: state) := gen_heap_interp p.(heap). 


  Class LibInterface := {
      libM: FairModel;
      libEM: ExtModel libM (fmrole libM);
      lib_step_ex_dec :> forall st ρ, Decision (exists st', fmtrans libM st (Some ρ) st');
      reset_lib := @ETs _ _ libEM;
      lib_reset_dom: forall ρ st, in_dom_rel (reset_lib ρ) st <-> ¬ role_enabled_model ρ st;
      lib_reset_cod: forall ρ st, in_cod_rel (reset_lib ρ) st -> role_enabled_model ρ st;
      lib_strong_lr: FM_strong_lr libM;

      libGSPre: gFunctors -> Set;
      libGS: gFunctors -> Set;
      lib_msi `{libGS Σ}: fmstate libM -> iProp Σ;
      lib_pre `{libGS Σ}: fmrole libM -> iProp Σ;
      lib_post `{libGS Σ}: fmrole libM -> iProp Σ;
      lib_st0: fmstate libM;
      lib_init `{l0: libGSPre Σ}: ⊢ ∀ ρ, |==> ∃ (l: libGS Σ), lib_msi lib_st0 (libGS0 := l) ∗ lib_post ρ (libGS0 := l);
      lib_post_dis `{l: libGS Σ}: ⊢ ∀ ρ st, lib_msi st (libGS0 := l) ∗ lib_post ρ (libGS0 := l) → ⌜ ¬ role_enabled_model ρ st ⌝;
      lib_reset `{l: libGS Σ}:
        ⊢ ∀ st st' ρ,
                   lib_msi st (libGS0 := l) -∗ lib_post ρ (libGS0 := l) -∗
                   ⌜ reset_lib ρ st st' ⌝
                   ==∗
                   lib_msi st' (libGS0 := l) ∗ lib_pre ρ (libGS0 := l);

      lib_step_restr (δ1 δ2: fmstate libM) := live_roles _ δ2 ⊆ live_roles _ δ1;
      ewp'_lib `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM} `{l: libGS Σ} := ewp'
          (PI := PI)
          (MSI := lib_msi (libGS0 := l))
          (step_restr := lib_step_restr);

      E__lib: coPset;
      lib_fun: val;
      lib_spec `{l: libGS Σ} `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM}
        (ρ: fmrole libM): 
      ⊢ (□ ∀ Φ,
             (lib_pre ρ (libGS0 := l)) -∗
              ▷ (∀ y, lib_post ρ (libGS0 := l) -∗ Φ y) -∗
              @ewp _ _ _ _ (ewp'_lib (l := l)) NotStuck E__lib ρ (lib_fun #()) Φ);
      lib_fun_nonval: to_val lib_fun = None;
  }.

End LibInterface.

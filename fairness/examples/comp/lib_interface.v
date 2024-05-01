From iris.bi Require Import bi.
From trillium.fairness.heap_lang Require Import lang.
From trillium.fairness Require Import fairness.
From trillium.fairness.ext_models Require Import ext_models.

Section LibInterface.

  Definition in_dom_rel {A: Type} (R: relation A) :=
    fun x => exists y, R x y. 

  Definition in_cod_rel {A: Type} (R: relation A) :=
    fun y => exists x, R x y. 

  Class LibInterface := {
      libM: FairModel;
      libEM: ExtModel libM (fmrole libM);
      lib_step_ex_dec :> forall st ρ, Decision (exists st', fmtrans libM st (Some ρ) st');
      reset_lib := @ETs _ _ libEM;
      lib_reset_dom: forall ρ st, in_dom_rel (reset_lib ρ) st <-> ¬ role_enabled_model ρ st;
      lib_strong_lr: FM_strong_lr libM;

      libGSPre: gFunctors -> Set;
      libGS: gFunctors -> Set;
      lib_msi `{libGS Σ}: fmstate libM -> iProp Σ;
      lib_fun: val heap_lang;
      lib_pre `{libGS Σ}: fmrole libM -> iProp Σ;
      lib_post `{libGS Σ}: fmrole libM -> iProp Σ;
      lib_st0: fmstate libM;
      lib_init `{l0: libGSPre Σ}: ⊢ ∀ ρ, |==> ∃ (l: libGS Σ), lib_msi lib_st0 (libGS0 := l) ∗ lib_post ρ (libGS0 := l);
      lib_post_dis `{l: libGS Σ}: ⊢ ∀ ρ st, lib_msi st (libGS0 := l) ∗ lib_post ρ (libGS0 := l) → ⌜ ¬ role_enabled_model ρ st ⌝;
      lib_reset `{l: libGS Σ}:
        ⊢ ∀ st ρ, lib_msi st (libGS0 := l) ∗ lib_post ρ (libGS0 := l) ==∗
                   ∃ st', lib_msi st' (libGS0 := l) ∗ lib_pre ρ (libGS0 := l);
  }.

End LibInterface.

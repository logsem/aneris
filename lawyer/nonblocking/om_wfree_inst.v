From iris.proofmode Require Import tactics.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import env_helpers obligations_model.
From lawyer.nonblocking.logrel Require Import logrel.
From lawyer.nonblocking Require Import wait_free_spec_defs.


Definition WF_Degree := bounded_nat 2.
Definition WF_Level := unit.
Definition WF_SB := 2.

Instance OPP_WF: ObligationsParamsPre WF_Degree WF_Level WF_SB.
esplit; try by apply _.
- apply nat_bounded_PO.
- apply unit_PO.
Defined.


Instance OP_HL_WF: OP_HL WF_Degree WF_Level WF_SB := {| om_hl_OPRE := OPP_WF |}.


Definition d_wfr0: WF_Degree. refine (ith_bn 2 0 _). abstract lia. Defined.
Definition d_wfr1: WF_Degree. refine (ith_bn 2 1 _). abstract lia. Defined.
Definition l_wfr: WF_Level := tt.


Declare Scope WFR_scope.

Notation "'d0'" := (d_wfr0) : WFR_scope.
Notation "'d1'" := (d_wfr1) : WFR_scope.
Notation "'l0'" := (l_wfr) : WFR_scope.

Notation "'Degree'" := (WF_Degree) : WFR_scope.
Notation "'Level'" := (WF_Level) : WFR_scope.



From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources.


Lemma foo:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ},
    heap1GS Σ.
Proof using.
  intros.
  exact (iem_phys _ EM).
  Show Proof.
  Abort. 

Lemma foo:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ},
    invGS_gen HasNoLc Σ.
Proof using.
  intros.
  apply _.
  Show Proof. 
Abort. 


(** Lawyer representation of wait-freedom of a "first-order" function `m`.
    Consists of two specs: model-based and physical-only.
    Neither of them restricts the arguments that `m` is called with.
    With that, the model-based spec implies that `m` must safely terminate with any argument while preserving physical and model interpretation, as well as invariants.
    Physical-only spec requires that physical interpretation and invariants are preserved, while allowing `m` to get stuck (however, since it satisfies the model-based spec, it won't actually get stuck).
    Both specifications rely on the module invariant `wfs_mod_inv`.
    It is crucial that this invariant doesn't involve any model resources (compare e.g. Σ restrictions for the invariant and the model-based spec).
    That's because it has to be preserved when either of the specs is used. *)
Record WaitFreeSpec (s: stuckness) (m: val) := {
  wfs_is_init_st: cfg heap_lang -> Prop;
  (** for wait-free modules, we expect that invariant doesn't contain OM resources *)
  wfs_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ;
  wfs_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} ::
    Persistent wfs_mod_inv;
  wfs_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}:
    forall c (INIT: wfs_is_init_st c),
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfs_mod_inv;

  
  (* wfs_F: nat; *)
  wfs_F: val -> nat;
  (* TODO: relax to non-trivial degrees? *)
  wfs_spec:
  forall {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ},
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv) ⊢
    wait_free_method s m d_wfr0 wfs_F;

  wfs_safety_spec:
    ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ},
      wfs_mod_inv ⊢ interp m;
}.

Program Definition WFS_weaken m (WFS: WaitFreeSpec NotStuck m): WaitFreeSpec MaybeStuck m := {|
  wfs_init_mod _ _ _ := wfs_init_mod _ _ WFS; 
  wfs_safety_spec _ _ _ := wfs_safety_spec _ _ WFS; 
  wfs_F := wfs_F _ _ WFS; 
|}.
Final Obligation. 
  simpl. intros.
  iIntros "#?". rewrite /wait_free_method.
  iIntros (**).
  iIntros (?) "!> (?&?) POST".
  iApply wp_stuck_weaken.
  iApply (wfs_spec _ _ WFS with "[] [-POST]"); iFrame "#∗".
Qed.


Definition ho_arg_restr {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
   s
  (f: val) (P: val -> Prop) (F: val -> nat) (fa: val) : iProp Σ :=
  ∃ a, ⌜ fa = PairV f a /\ P a ⌝ ∗ wait_free_method s f d_wfr0 F. 

Record WaitFreeSpecHO (s: stuckness) (m: val) (P: val -> Prop) := {
  wfsho_is_init_st: cfg heap_lang -> Prop;
  (** for wait-free modules, we expect that invariant doesn't contain OM resources *)
  wfsho_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ;
  wfsho_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} ::
    Persistent wfsho_mod_inv;
  wfsho_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}:
    forall c (INIT: wfsho_is_init_st c),
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfsho_mod_inv;


  (** The amount of fuel consumed by higher-order function is determined by:
      - amount of fuel consumed by its function argument
      - the actual argument (e.g. length of the list) *)
  wfsho_F_fun: (val -> nat) -> val -> nat;
  (** We assume our higher-order function `m` in the uncurried form, e.g.
        list_map x = let '(f, l) = x in ...
      Then, we consider the calls of form `m (f, a)`, where `f` is an arbitrary (first-order) function and `a` fits the additional restriction (e.g. being a list).
      For `f`, we assume that the first-order wait-free Trillium spec holds.
      With that, if enough fuel is provided, the call must safely terminate. *)
  wfsho_spec:
  forall {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    (f: val) (F_inner: val -> nat),
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfsho_mod_inv) ⊢
    wait_free_method_gen s m d_wfr0 (wfsho_F_fun F_inner)
      (ho_arg_restr s f P F_inner) (fun _ => emp);

  (** Contrary to the Lawyer spec above, physical-only spec doesn't place any restrictions on the argument (besides satisfying LR for values).
      That's because in an arbitrary client, `m` can be called with any argument before the "target" call (considered by the adequacy theorem) happens.
      We expect that `m` will get stuck if the argument doesn't fit the form defined in ho_arg_restr (e.g. when an argument to list_map is not a pair of some function and a list). 
   *)
  wfsho_safety_spec:
    ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ},
      wfsho_mod_inv ⊢ interp m;
}. 


(** WIP; should become a generalization of both specs above *)
Record WaitFreeSpecGen (m: val)
  (WF_P WF_Q: forall {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}, val -> iProp Σ)
  := {
  (* wfs_is_init_st: cfg heap_lang -> Prop; *)
  (* (** for wait-free modules, we expect that invariant doesn't contain OM resources *) *)
  (* wfs_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ; *)
  (* wfs_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} :: *)
  (*   Persistent wfs_mod_inv; *)
  (* wfs_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}: *)
  (*   forall c (INIT: wfs_is_init_st c), *)
  (*     ⊢ hl_phys_init_resource c ={⊤}=∗ wfs_mod_inv; *)
  (* wfs_F: nat; *)
  (* wfs_spec: *)
  (* forall {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}, *)
  (*   (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv) ⊢ *)
  (*   wait_free_method m d_wfr0 wfs_F; *)

  (* (* TODO: derive it from wfs_spec *) *)
  (* wfs_safety_spec: *)
  (*   ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ}, *)
  (*     wfs_mod_inv ⊢ interp m; *)    
}.


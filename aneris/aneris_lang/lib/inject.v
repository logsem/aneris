From aneris.aneris_lang Require Export lang.
Import ast.
Class Inject (A B : Type) := {
  inject : A → B;
  inject_inj : Inj (=) (=) inject;
}.

Notation "$ x" := (inject x) (at level 8).
#[global] Existing Instance inject_inj.

#[global] Program Instance Inject_option `{!Inject T val} : Inject (option T) val :=
  {| inject := λ o, if o is Some t then SOMEV $t else NONEV |}.
Next Obligation. auto. Qed.
Next Obligation.
  intros ? [] [] [] [=]; [|done]. f_equal. by eapply (inj _).
Qed.

#[global] Program Instance Inject_prod `{!Inject A val, !Inject B val} :
  Inject (A * B) val := {| inject := (λ '(t1, t2), PairV $t1 $t2) |}.
Next Obligation. intros ? [] ? [] [] [] [=]. f_equal; by apply (inj _). Qed.

#[global] Program Instance Inject_sum `{!Inject A val, !Inject B val} : Inject (A + B) val
  := {| inject := λ s, match s with
                       | inl v => InjLV $v
                       | inr v => InjRV $v
                       end |}.
Next Obligation. by intros ? [] ? [] [] [] [= ->%(inj _)]. Qed.

#[global] Program Instance : Inject Z val := {| inject := LitV ∘ LitInt |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject nat val := {| inject := inject ∘ Z.of_nat |}.

#[global] Program Instance : Inject socket_address val :=
  {| inject := LitV ∘ LitSocketAddress |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject string val := {| inject := LitV ∘ LitString |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject bool val := {| inject := LitV ∘ LitBool |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject unit val := {| inject := λ _, #() |}.
Next Obligation. by intros [] []. Qed.

#[global] Program Instance : Inject loc val := {| inject := LitV ∘ LitLoc |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance Inject_expr `{!Inject A val} : Inject A expr :=
  {| inject := Val ∘ inject |}.

#[global] Program Instance : Inject val val := {| inject := id |}.

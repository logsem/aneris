
(* copied from coq-hahn. Probably can be replaced by o* tactics of stdpp *)

Tactic Notation "forward" tactic1(tac) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|].

Tactic Notation "forward" tactic1(tac) "as" simple_intropattern(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|intros H].

Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].

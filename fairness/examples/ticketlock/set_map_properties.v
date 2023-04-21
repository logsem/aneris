From trillium.prelude Require Export quantifiers.
From iris.bi Require Import bi.



(* TODO: move into stdpp *)
Section SetMapProperties.

  Lemma set_map_compose_gset {A1 A2 A3: Type}
    `{EqDecision A1} `{EqDecision A2} `{EqDecision A3}
    `{Countable A1} `{Countable A2} `{Countable A3}
    (f: A2 -> A3) (g: A1 -> A2) (m: gset A1):
    set_map (f ∘ g) m (D:=gset _) = set_map f (set_map g m (D:= gset _)).
  Proof using.
    set_solver. 
  Qed. 

  Lemma elem_of_map_inj_gset {A B} 
    `{EqDecision A} `{Countable A}
    `{EqDecision B} `{Countable B}
    (f: A -> B) (m: gset A) (a: A) (INJ: injective f):
    a ∈ m <-> f a ∈ set_map f m (D := gset _).
  Proof using.
    split; [apply elem_of_map_2| ].
    intros IN. apply elem_of_map_1 in IN as (a' & EQ & IN).
    apply INJ in EQ. congruence. 
  Qed.
    
End SetMapProperties.

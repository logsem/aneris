From aneris.aneris_lang Require Import ast aneris_lifting.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.spec Require Import crdt_base.

Section gcpt_code_wrapper.

  Context `{!CRDT_Params}.

  Definition gcpt_init_st : val :=
    λ: <>, vect_make #(length CRDT_Addresses) #0.

Definition list_map2 : val :=
  rec: "list_map2" "f" "l" "l'" :=
  match: "l" with
    SOME "a" =>
    match: "l'" with
      SOME "b" =>
      "f" (Fst "a") (Fst "b") :: "list_map2" "f" (Snd "a") (Snd "b")
    | NONE => assert: #false
    end
  | NONE => NONE
  end.

Definition gcpt_mutator : val :=
  λ: "repId" "st" "op",
  match: list_nth "st" "repId" with
    NONE => "st"
  | SOME "p" => vect_update "st" "repId" ("op" + "p")
  end.

Definition max_fn : val := λ: "i" "j", (if: "i" < "j"
                            then  "j"
                            else  "i").

Definition gcpt_merge : val := λ: "st" "st'", list_map2 max_fn "st" "st'".

Definition gcpt_crdt : val :=
    λ: <>, ((gcpt_init_st, gcpt_mutator), gcpt_merge).

Definition gcpt_init : val :=
  λ: "addrs" "rid",
  let: "len" := list_length "addrs" in
  let: "initRes" := statelib_init
                      vect_serialize vect_deserialize
                      "addrs" "rid" gcpt_crdt in
  let: "get_state" := Fst "initRes" in
  let: "update" := Snd "initRes" in
  ("get_state", "update").

End gcpt_code_wrapper.

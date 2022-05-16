From aneris.aneris_lang Require Import lang.

Definition inj_get_left : val :=
  λ: "v",
    match: "v" with
      InjL "w" => "w"
    | InjR "_" => assert: #false
    end.

Definition inj_get_right : val :=
  λ: "v",
    match: "v" with
      InjL "_" => assert: #false
    | InjR "w" => "w"
    end.

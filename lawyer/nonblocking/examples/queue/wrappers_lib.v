From heap_lang Require Import lang notation.


Definition val_is_int {Σ: gFunctors} (v: val): iProp Σ := ⌜ ∃ (n: Z), v = #n ⌝.

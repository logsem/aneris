From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
Set Default Proof Using "Type".

(** * Adapted from Perennial: https://github.com/mit-pdos/perennial/blob/master/src/program_logic/atomic_fupd.v *)

(*
MIT License

Copyright (c) 2021

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*)

(** Sugar for TaDA-style logically atomic specs. We only have the variants we need. *)
(** Use [fupd_mask_intro] if you are stuck with non-matching masks. *)

(* Note regarding the use of '∖Eo%I%I%I%I' below:
   Coq insists that in a notation, if a nonterminal (like Eo) is used multiple times,
   it must be under the exact same scope stack each time. Some Iris notations add %I to their nonterminals to ensure
   they remain in the iris scope. Eo is used below by different Iris connectives, meaning different numbers
   of these implicit %Is, and that difference has to be compensated by adding some explicit %I *)

(* TODO: explain how our version differs from Perennial's (specifically, our use of masks) *)

(** With ▷ around the linearization point **)

(* Full variant *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ E,
        ⌜Eo ⊆ E⌝ -∗
        P -∗ (|={⊤,E}=> ▷ ∃ x1, .. (∃ xn,
                α ∗
                ∀ y1, .. (∀ yn, β -∗ |={E,⊤}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

(* No RET binders. *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ E,
        ⌜Eo ⊆ E⌝ -∗
        (|={⊤,E}=> ▷ ∃ x1, .. (∃ xn,
              α ∗
              ∀ y1, .. (∀ yn, β -∗ |={E,⊤}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

(* No RET binders. Return value determined together with fancy update. *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' ∃∃ y1 .. yn , 'RET' v ; β '>>>'" :=
  (□ ∀ Φ E,
        ⌜ Eo ⊆ E ⌝ -∗
        (|={⊤, E%I%I%I%I}=> ▷ ∃ x1, .. (∃ xn,
              α ∗
              ∀ y1, .. (∀ yn, β -∗ |={E, ⊤}=> Φ v%V) .. ) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  'RET' v ; '/' β ']' '>>>' ']'")
  : bi_scope.

(* No post-quantifiers binders *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' 'RET' v ; β '>>>'" :=
  (□ ∀ Φ E,
        ⌜ Eo ⊆ E ⌝ -∗
        (|={⊤, E%I%I%I%I}=> ▷ ∃ x1, .. (∃ xn,
              α ∗
              (β -∗ |={E%I%I, ⊤}=> Φ v%V)) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' 'RET' v ; '/' β ']' '>>>' ']'")
  : bi_scope.

(* Full variant minus post quantification *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ E,
        ⌜Eo ⊆ E⌝ -∗
        P -∗ (|={⊤,E}=> ▷ ∃ x1, .. (∃ xn,
                α ∗
                (β -∗ |={E,⊤}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

(* Full variant minus post quantification and return binders*)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ E,
        ⌜Eo ⊆ E⌝ -∗
        P -∗ (|={⊤,E}=> ▷ ∃ x1, .. (∃ xn,
                α ∗
                (β -∗ |={E,⊤}=> (Q -∗ Φ v%V))) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' '/' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

(* Full variant min return binders *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<▷' ∃∃ y1 .. yn , β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ E,
        ⌜Eo ⊆ E⌝ -∗
        P -∗ (|={⊤,E}=> ▷ ∃ x1, .. (∃ xn,
                α ∗
                ∀ y1, .. (∀ yn, β -∗ |={E,⊤}=> (Q -∗ Φ v%V)) .. ) .. ) -∗
          WP e @[ip] ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @[ ip ]  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '['   RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

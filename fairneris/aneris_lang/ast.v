From stdpp Require Export binders.


(** Basic Network *)
Definition ip_address := string.

Definition port := positive.

Inductive socket_address :=
| SocketAddressInet (address : ip_address) (port : positive).

Definition ip_of_address (sa : socket_address) : ip_address :=
  match sa with
  | SocketAddressInet ip _ => ip
  end.
Definition port_of_address (sa : socket_address) : positive :=
  match sa with
  | SocketAddressInet _ p => p
  end.

Record socket := mkSocket {
  saddress : option socket_address;
  sblock : bool;
}.

(** Grammar of AnerisLang *)
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Open Scope Z_scope.

Definition socket_handle := positive.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc)
| LitString (s : string)
| LitSocket (s : socket_handle) | LitSocketAddress (s : socket_address).
Inductive un_op : Set :=
| NegOp | MinusUnOp | StringOfInt | IntOfString | StringLength.
Inductive bin_op : Set :=
| PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
| AndOp | OrOp | XorOp (* Bitwise *)
| ShiftLOp | ShiftROp (* Shifts *)
| LeOp | LtOp | EqOp (* Relations *)
| StringApp.

Inductive expr :=
(* Values *)
| Val (v : val)
(* Base lambda calculus *)
| Var (x : string)
| Rec (f x : binder) (e : expr)
| App (e1 e2 : expr)
(* Base types and their operations *)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| If (e0 e1 e2 : expr)
| FindFrom (e0 e1 e2 : expr)
| Substring (e0 e1 e2 : expr)
| Rand (e : expr)
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : expr) (e2 : expr)
(* Node-local concurrency *)
| Fork (e : expr)
(* Heap *)
| Alloc (lbl : option string) (e : expr)
| Load (e : expr)
| Store (e1 : expr) (e2 : expr)
| CAS (e0 : expr) (e1 : expr) (e2 : expr)
(* Sockets/Network *)
| MakeAddress (e1 : expr) (e2 : expr)
| GetAddressInfo (e : expr)
| NewSocket (e : expr)
| SocketBind (e1 : expr) (e2 : expr)
| SendTo (e1 : expr) (e2 : expr) (e3 : expr)
| SendToRepeat (e1 : expr) (e2 : expr) (e3 : expr)
| ReceiveFrom (e1 : expr)
| SetReceiveTimeout (e1 : expr) (e2 e3 : expr)
| Start (ip : base_lit) (e : expr)

with val :=
| LitV (l : base_lit)
| RecV (f x : binder) (e : expr)
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** Notations for some derived forms *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).

Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation i2s e := (UnOp StringOfInt e)%E (only parsing).
Notation s2i e := (UnOp IntOfString e)%E (only parsing).
Notation strlen e := (UnOp StringLength e)%E (only parsing).

Notation "½" := (1/2)%Qp.
Notation "¼" := (1/4)%Qp.
Notation "¾" := (3/4)%Qp.

Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
Coercion LitSocketAddress : socket_address >-> base_lit.
Coercion LitString : string >-> base_lit.

Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion Var : string >-> expr.

(* Note that the scope for expressions and values are NOT the same:
   Expressions have brackets that comes from the sequence \<, with name
   MATHEMATICAL LEFT ANGLE BRACKET where as values has brackets
   that come from \〈 (name: LEFT-POINTING ANGLE BRACKET) *)
(* Notation "⟨ n ; e ⟩" := (mkExpr n e) (at level 0, right associativity). *)
(* Notation "〈 n ; v 〉" := (mkVal n v%V). *)

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>

  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
 *)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref<<' lbl '>>' e" := (Alloc (Some lbl%string) e%E) (at level 10) : expr_scope.
Notation "'ref' e" := (Alloc None e%E) (at level 10) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ^^ e2" := (BinOp StringApp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.
Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%E e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']'  ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (LitV (LitBool false))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (LitV (LitBool true)) e2%E) (only parsing) : expr_scope.

(** Notations for option *)
Notation NONE := (InjL #()) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation NONEV := (InjLV #()) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing).


(* Shortcut for recursive definitions *)
Notation "'letrec:' f x := e1 'in' e2" :=
  (Lam f%binder e2%E (Rec f%binder x%binder e1%E))
  (at level 200, f at level 1, x at level 1, e1, e2 at level 200,
   format "'[' 'letrec:'  f  x  :=  '/  ' '[' e1 ']'  'in'  '/' e2 ']'")
  : expr_scope.

Notation "'letrec:' f x y .. z := e1 'in' e2" :=
  (Lam f%binder e2%E
     (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e1%E) ..)))
  (at level 200, f at level 1, x,y,z at level 1, e1, e2 at level 200,
   format "'[' 'letrec:'  f  x y .. z :=  '/  ' '[' e1 ']'  'in'  '/' e2 ']'")
  : expr_scope.

(** Constructions on top of the language *)

(** Serializer data type *)
Record serializer :=
  { s_ser : val;
    s_deser : val }.


(** Assert construction *)
Definition assert : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)

Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

(** Mutex implementation using CAS *)
Definition newlock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.

(** Shim for monitors. *)

Definition new_monitor_def : val
  := λ: <>, (#(), newlock #()).
Definition monitor_try_acquire_def : val
  := λ: "mon", try_acquire (Snd "mon").
Definition monitor_acquire_def : val
  := λ: "mon", acquire (Snd "mon").
Definition monitor_release_def : val
  := λ: "mon", release (Snd "mon").
Definition monitor_signal_def : val
  := λ: "mon", #().
Definition monitor_broadcast_def : val
  := λ: "mon", #().
Definition monitor_wait_def : val
  := λ: "mon",
       release (Snd "mon");;
       acquire (Snd "mon").

Definition new_monitor_aux : seal (new_monitor_def).
  by eexists. Qed.
Definition new_monitor :=
  new_monitor_aux.(unseal).
Definition new_monitor_eq : new_monitor = new_monitor_def
  := new_monitor_aux.(seal_eq).

Definition monitor_try_acquire_aux : seal (monitor_try_acquire_def).
  by eexists. Qed.
Definition monitor_try_acquire
  := monitor_try_acquire_aux.(unseal).
Definition monitor_try_acquire_eq : monitor_try_acquire = monitor_try_acquire_def
  := monitor_try_acquire_aux.(seal_eq).

Definition monitor_acquire_aux : seal (monitor_acquire_def).
  by eexists. Qed.
Definition monitor_acquire
  := monitor_acquire_aux.(unseal).
Definition monitor_acquire_eq : monitor_acquire = monitor_acquire_def
  := monitor_acquire_aux.(seal_eq).

Definition monitor_release_aux : seal (monitor_release_def).
  by eexists. Qed.
Definition monitor_release
  := monitor_release_aux.(unseal).
Definition monitor_release_eq : monitor_release = monitor_release_def
  := monitor_release_aux.(seal_eq).

Definition monitor_signal_aux : seal (monitor_signal_def).
  by eexists. Qed.
Definition monitor_signal
  := monitor_signal_aux.(unseal).
Definition monitor_signal_eq : monitor_signal = monitor_signal_def
  := monitor_signal_aux.(seal_eq).

Definition monitor_broadcast_aux : seal (monitor_broadcast_def).
  by eexists. Qed.
Definition monitor_broadcast
  := monitor_broadcast_aux.(unseal).
Definition monitor_broadcast_eq : monitor_broadcast = monitor_broadcast_def
  := monitor_broadcast_aux.(seal_eq).

Definition monitor_wait_aux : seal (monitor_wait_def).
  by eexists. Qed.
Definition monitor_wait
  := monitor_wait_aux.(unseal).
Definition monitor_wait_eq : monitor_wait = monitor_wait_def
  := monitor_wait_aux.(seal_eq).

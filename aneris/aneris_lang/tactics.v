From aneris.aneris_lang Require Export lang.
Set Default Proof Using "Type".
Import base_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                                 => tac K e
    | App ?e1 (Val ?v)                  => add_item (AppLCtx v) K e1
    | App ?e1 ?e2                       => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e                       => add_item (UnOpCtx op) K e
    | BinOp ?op ?e0 (Val ?v1)           => add_item (BinOpLCtx op v1) K e0
    | BinOp ?op ?e0 ?e1                 => add_item (BinOpRCtx op e0) K e1
    | FindFrom ?e0 (Val ?v1) (Val ?v2)  => add_item (FindFromLCtx v1 v2) K e0
    | FindFrom ?e0 ?e1 (Val ?v2)        => add_item (FindFromMCtx e0 v2) K e1
    | FindFrom ?e0 ?e1 ?e2              => add_item (FindFromRCtx e0 e1) K e2
    | Substring ?e0 (Val ?v1) (Val ?v2) => add_item (SubstringLCtx v1 v2) K e0
    | Substring ?e0 ?e1 (Val ?v2)       => add_item (SubstringMCtx e0 v2) K e1
    | Substring ?e0 ?e1 ?e2             => add_item (SubstringRCtx e0 e1) K e2
    | Rand ?e                           => add_item RandCtx K e
    | If ?e0 ?e1 ?e2                    => add_item (IfCtx e1 e2) K e0
    | Pair ?e1 (Val ?v )                => add_item (PairLCtx v) K e1
    | Pair ?e1 ?e2                      => add_item (PairRCtx e1) K e2
    | Fst ?e                            => add_item FstCtx K e
    | Snd ?e                            => add_item SndCtx K e
    | InjL ?e                           => add_item InjLCtx K e
    | InjR ?e                           => add_item InjRCtx K e
    | Case ?e0 ?e1 ?e2                  => add_item (CaseCtx e1 e2) K e0
    | Alloc ?lbl ?e                     => add_item (AllocCtx lbl) K e
    | Load ?e                           => add_item LoadCtx K e
    | Store ?e0 (Val ?v1)               => add_item (StoreLCtx v1) K e0
    | Store ?e0 ?e1                     => add_item (StoreRCtx e0) K e1
    | CAS ?e0 (Val ?v1) (Val ?v2)       => add_item (CasLCtx v1 v2) K e0
    | CAS ?e0 ?e1 (Val ?v2)             => add_item (CasMCtx e0 v2) K e1
    | CAS ?e0 ?e1 ?e2                   => add_item (CasRCtx e0 e1) K e2
    | MakeAddress ?e0 (Val ?v1)         => add_item (MakeAddressLCtx v1) K e0
    | MakeAddress ?e0 ?e1               => add_item (MakeAddressRCtx e0) K e1
    | NewSocket ?e0 (Val ?v1) (Val ?v2) => add_item (NewSocketLCtx v1 v2) K e0
    | NewSocket ?e0 ?e1 (Val ?v2)       => add_item (NewSocketMCtx e0 v2) K e1
    | NewSocket ?e0 ?e1 ?e2             => add_item (NewSocketRCtx e0 e1) K e2
    | SocketBind ?e0 (Val ?v1)          => add_item (SocketBindLCtx v1) K e0
    | SocketBind ?e0 ?e1                => add_item (SocketBindRCtx e0) K e1
    | SetReceiveTimeout ?e0 (Val ?v1) (Val ?v2)
                                        => add_item (SetReceiveTimeoutLCtx v1 v2) K e0
    | SetReceiveTimeout ?e0 ?e1 (Val ?v2)
                                        => add_item (SetReceiveTimeoutMCtx e0 v2) K e1
    | SetReceiveTimeout ?e0 ?e1 ?e2     => add_item (SetReceiveTimeoutRCtx e0 e1) K e2
    | SendTo ?e0 (Val ?v1) (Val ?v2)    => add_item (SendToLCtx v1 v2) K e0
    | SendTo ?e0 ?e1 (Val ?v2)          => add_item (SendToMCtx e0 v2) K e1
    | ReceiveFrom ?e                    => add_item ReceiveFromCtx K e
    end
  with add_item Ki K e := go (Ki :: K) e
  in
  go (@nil ectx_item) e.

open Ast
open List_code
open Network_util_code

let int_ser v = i2s v

let int_deser v = unSOME (s2i v)

let int_serializer : int serializer =
  { s_ser   = int_ser;
    s_deser = int_deser }

let bool_ser v = i2s (if v then 1 else 0)

let bool_deser v = let i = s2i v in
                   if i = Some 1 then true
                   else false

let bool_serializer : bool serializer =
  { s_ser   = bool_ser;
    s_deser = bool_deser }

let unit_ser =
  fun _u -> ""

let unit_deser =
  fun _s -> ()

let unit_serializer : unit serializer =
  { s_ser   = unit_ser;
    s_deser = unit_deser }

let string_ser =
  fun x -> x

let string_deser =
  fun x -> x

let string_serializer =
  { s_ser   = string_ser;
    s_deser = string_deser }

let prod_ser (serA[@metavar "val"]) (serB[@metavar "val"]) =
  fun v ->
  let s1 = serA (fst v) in
  let s2 = serB (snd v) in
  (i2s (strlen s1)) ^ "_" ^ s1 ^ s2

let prod_deser (deserA[@metavar "val"]) (deserB[@metavar "val"]) =
  fun s ->
    match findFrom s 0 '_' with
      Some i ->
      let len = unSOME (s2i (substring s 0 i)) in
      let s1 = substring s (i + 1) len in
      let s2 = substring s (i + 1 + len)
                             (strlen s - (i + 1 + len)) in
      let v1 = deserA s1 in
      let v2 = deserB s2 in
      (v1, v2)
    | None -> assert false

let prod_serializer
      (sA[@metavar "serializer"] : 'a serializer) (sB[@metavar "serializer"] : 'b serializer)
    : ('a * 'b) serializer =
  { s_ser   = prod_ser sA.s_ser sB.s_ser ;
    s_deser = prod_deser sA.s_deser sB.s_deser }


let saddr_ser s =
  prod_ser string_ser int_ser (get_address_info s)

let saddr_deser s =
  let ipp = prod_deser string_deser int_deser s in
  (makeAddress (fst ipp) (snd ipp))

let saddr_serializer =
  { s_ser   = saddr_ser ;
    s_deser = saddr_deser }

let sum_ser  (serA[@metavar "val"]) (serB[@metavar "val"])  =
    fun v ->
    match v with
      InjL x -> "L" ^ "_" ^ serA x
    | InjR x -> "R" ^ "_" ^ serB x

 let sum_deser (deserA[@metavar "val"]) (deserB[@metavar "val"]) =
   fun s ->
   let tag = substring s 0 2 in
   let rest = substring s 2 (strlen s - 2) in
   if tag = "L_" then
     InjL (deserA rest)
   else
     if tag = "R_" then
       InjR (deserB rest)
     else
       assert false

 let sum_serializer
       (sA[@metavar "serializer"] : 'a serializer)
       (sB[@metavar "serializer"] : 'b serializer)
     : ('a, 'b) sumTy serializer =
   { s_ser   = sum_ser sA.s_ser sB.s_ser ;
     s_deser = sum_deser sA.s_deser sB.s_deser }

let option_ser  (ser[@metavar "val"])  =
    fun v ->
    match v with
      None -> "L" ^ "_" ^ ""
    | Some x -> "R" ^ "_" ^ ser x

 let option_deser (deser[@metavar "val"]) =
   fun s ->
   let tag = substring s 0 2 in
   let rest = substring s 2 (strlen s - 2) in
   if tag = "L_" then
     None
   else
     if tag = "R_" then
       Some (deser rest)
     else
       assert false

let option_serializer (s[@metavar "serializer"]) =
  { s_ser   = option_ser s.s_ser ;
    s_deser = option_deser s.s_deser }

 let list_ser (ser[@metavar "val"])  =
   let rec list_ser v =
     match v with
       Some a ->
        let hd = ser (fst a) in
        let tl = list_ser (snd a) in
        (i2s (strlen hd)) ^ "_" ^ hd ^ tl
     | None -> ""
   in list_ser

 let list_deser (deser[@metavar "val"]) =
   let rec list_deser s =
     match findFrom s 0 '_' with
       Some i ->
        let len = unSOME (s2i (substring s 0 i)) in
        let h = substring s (i + 1) len in
        let t = substring s (i + 1 + len)
                   (strlen s - (i + 1 + len)) in
        let hd  = deser h in
        let tail = list_deser t in
        list_cons hd tail
     | None -> None
   in list_deser

 let list_serializer
       (s[@metavar "serializer"] : 'a serializer) : 'a alist serializer =
  { s_ser   = list_ser s.s_ser ;
    s_deser = list_deser s.s_deser }

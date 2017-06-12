(* the database encoding of values is slightly different from the AST's.
 * Entries must be indexed by their corresponding atom and arity, and
 * they might either point to clauses or predicates. *)

exception UndefinedValue

module HT = Hashtbl

open Ast

type context = atom
let default_context = -1

module Key = struct
  type t = { context : atom; name : atom; arity : int }
  let make context name arity = { context; name; arity }
  let context k = k.context
  let name k = k.name
  let arity k = k.arity
  let hash = Hashtbl.hash
  let compare = Pervasives.compare
end

open Key
type key = Key.t

type clause = pred * arg option (* optional sequent *)

type entry = clause list ref

let key_of_predicate context name args = { context; name; arity = List.length args }
let key_of_atom context name = { context; name; arity = 0 }
let key_of_operator = Key.make

let rec mkkey ?(context=default_context) : term -> key option = function
  | Clause ({ name;args },_)
  | Pred { name;args } -> Some (key_of_predicate context name args)
  | Atom name          -> Some (key_of_atom context name)
  | Var  _             -> None
  | Int  _             -> None

let keyname = fst
let keyarity = snd

let mkvalue = function
  | Pred p       -> p,None
  | Clause (p,s) -> p,Some s
  | Atom name    -> Ast.{ name; infix=false; args = [] }, None
  | _            -> assert false

type t = {
  clauses   : (key, entry) HT.t;
  operators : (key, OpKind.t * int) HT.t
}

let make () = {
  clauses   = HT.create 211;
  operators = HT.create 11;
}

let find r k =
  HT.find r.clauses k

let add_new r k v =
  HT.add r.clauses k (ref [mkvalue v])

let get_entry r k =
  find r k

let add_front r k v =
  try
    let l = get_entry r k in
    l := mkvalue v::!l
  with Not_found -> add_new r k v

let add_back r k v =
  try
    let l = get_entry r k in
    l := !l @ [mkvalue v]
  with Not_found -> add_new r k v

let remove_all r k =
  HT.remove r.clauses k

let remove_front r k =
  try
    let l = get_entry r k in
    match !l with
    | [] -> ()
    | x::xs -> l := xs
  with Not_found -> raise UndefinedValue

let remove_back r k =
  let rec drop_last l = function
    | [] -> List.rev l
    | [x] -> List.rev l
    | x::xs -> drop_last (x::l) xs in
  try
    let l = get_entry r k in
    match !l with
    | [] -> ()
    | xs -> l := drop_last [] xs
  with Not_found -> raise UndefinedValue

let find r k =
  try Some (find r k) with Not_found -> None

module Op = struct

  let infix r o =
    try Some (HT.find r.operators o) with Not_found -> None

  let is_infix r o =
    infix r o != None

  let add r o k l =
    HT.replace r.operators o (k,l)

end

module PP = struct
  open Fmt

  let key ppf k =
    fprintf ppf "%a/%d" Ast.PP.atom (Key.name k) (Key.arity k)

  let value ppf = function
    | p, None   -> fprintf ppf "%a" Ast.PP.term (Pred p)
    | p, Some s -> fprintf ppf "%a" Ast.PP.term (Clause (p,s))

  let entry ppf (k,v) =
    list ~pp_sep:(cut ".") value ppf !v

  let pp ppf reg =
    HT.iter (fun k v -> fprintf ppf "%a.@." entry (k,v)) reg.clauses

end

let display_ops reg =
  (* print out all the operator definitions *)
  let iterf ppf {context;name;arity} (kind,prec) =
    Fmt.fprintf ppf "@['%a'@] @[\t%a\t%d@]@\n" Ast.PP.atom name OpKind.pp kind prec in
  Fmt.eprintf "operators:@\n@[%a@]@." (fun ppf -> HT.iter (iterf ppf)) reg.operators

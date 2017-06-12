
module ST = StringStore

type atom = int
type var  = int * string
let is_instance = function (-1,_) -> false | _ -> true

type term    = Atom of atom | Int of int | Var of var | Pred of pred | Clause of clause
and  pred    = { name : atom; infix : bool; args : arg list }
and  arg     = term
and  clause  = pred * arg

type phrase = term

let int x = Int x
let atom x = Atom (ST.atom x)
let var x = Var x
let op x = ST.atom x

let pred ?(infix=false) name args =
  match name, args with
    ":-", [Pred a;b] -> Clause (a,b)
  | ":-", [Atom a;b] -> Clause ({name = a; infix=false; args=[]}, b)
  | _                -> Pred { name = ST.atom name;infix;args }

let rec term_bound v = function
  | Var x    -> x = v
  | Int _    -> false
  | Atom _   -> false
  | Pred p   -> pred_bound v p
  | Clause c -> clause_bound v c
and pred_bound v { args; _ } =
  List.exists (term_bound v) args
and clause_bound v (p,a) =
  pred_bound v p || term_bound v a

module VarMap = Map.Make(struct type t = var let compare = compare end)

module PP = struct

  open Fmt

  let list_sep sep = list ~pp_sep:(fun ppf () -> string ppf sep)

  let opt ppv ppf = function
    | None   -> fprintf ppf "None"
    | Some x -> fprintf ppf "Some %a" ppv x

  let int ppf x = fprintf ppf "%d" x
  let atom ppf x = string ppf (ST.string x)
  let var ppf (i,x) = if i = -1 then string ppf x else fprintf ppf "%s_%d" x i

  let list sep = list ~pp_sep:(fun ppf () -> atom ppf sep)

  let rec pred ppf { name; infix; args } =
    match infix, args with
    |    _, [] -> fprintf ppf "%a" atom name
    (*      | true,  _ -> fprintf ppf "%a" (list name term) args *)
    | _        -> fprintf ppf "'%a'(%a)" atom name (list_sep "," term) args
  and term ppf = function
    | Atom a -> atom ppf a
    | Int x  -> int ppf x
    | Var v  -> var ppf v
    | Pred p -> pred ppf p
    | Clause (p,s) -> fprintf ppf "%a :- %a" pred p term s

  let varmap pp_e ppf vs =
    let open Fmt in
    let l = VarMap.bindings vs in
    let pp_pair ppf (v,t) = fprintf ppf "@[%a = %a@]" var v pp_e t in
    fprintf ppf "%a" (list ~pp_sep:(cut ",") pp_pair) l

end

let rec term_vars l = function
  | Atom _ -> l
  | Int _  -> l
  | Var v  -> VarMap.add v v l
  | Pred p -> pred_vars l p
  | Clause (p,t) -> clause_vars l (p,t)
and clause_vars l (p,t) =
  term_vars (pred_vars l p) t
and pred_vars l p = List.fold_left term_vars l p.args

let ground vars x = vars VarMap.empty x = VarMap.empty

let term_ground = ground term_vars
and clause_ground = ground clause_vars
and pred_ground = ground pred_vars

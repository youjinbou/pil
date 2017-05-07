module Fmt = struct
  include Format
  let list = pp_print_list
  let string = pp_print_string
  let cut sep ppf () = fprintf ppf "%s@;" sep
end

module HT = Hashtbl

module CmdLine = struct

  open Arg

  let specs_ = ref []

  let add_params l =
    specs_ := l @ !specs_

  let specs () = !specs_

end

module Debug = struct

  let is_active = ref false

  let activate () =
    is_active := true

  let dbg_true = fun msg -> Fmt.eprintf msg
  let dbg_false = fun msg -> Fmt.(ifprintf err_formatter) msg

  let printf msg =
    if !is_active then dbg_true msg else dbg_false msg

  let _ =
    CmdLine.add_params [
      "-d", Arg.Unit activate, "activate debugging display";
    ]

end

let dbg = Debug.printf

type atom = int
type var  = string

module StringStore = struct

  module S = struct type t = string let equal x y = x = y let hash = HT.hash end
  module I = struct type t = int let equal x y = x == y let hash x = x end
  module StringMap = HT.Make(S)
  module IntMap = HT.Make(I)

  type t = { mutable c : int; addresses : int StringMap.t; strings : string IntMap.t }
  let store = { c = 0; addresses = StringMap.create 211; strings =  IntMap.create 211 }

  let atom x =
    try StringMap.find store.addresses x
    with Not_found -> let r = store.c in
                      store.c <- succ r;
                      StringMap.add store.addresses x r;
                      IntMap.add store.strings r x;
                      r
  let string x =
    IntMap.find store.strings x

  let strue = "true"
  let sfalse = "false"
  let scomma = ","
  let ssemicolon = ";"
  let sturnstile = ":-"
  let sequal = "="

  let true_ = atom strue
  let false_ = atom sfalse
  let comma = atom scomma
  let semicolon = atom ssemicolon
  let turnstile = atom sturnstile
  let equal = atom sequal

end

module Ast = struct

  type term   = Atom of atom | Var of var | Pred of pred | Clause of clause
  and  op     = Xfx | Xfy | Yfx | Fx | Fy | Xf | Yf

  and  pred   = { name : atom; infix : bool; args : arg list }
  and  arg    = term
  and  clause = pred * arg

  type phrase = term

  let atom x = Atom (StringStore.atom x)
  let var x = Var x
  let op x = StringStore.atom x

  let pred ?(infix=false) name args = Pred { name = StringStore.atom name;infix;args }
  let clause x y = Clause (x,y)

  module VarMap = Map.Make(struct type t = var let compare = compare end)

  module PP = struct

    open Fmt

    let list_sep sep = list ~pp_sep:(fun ppf () -> string ppf sep)

    let opt ppv ppf = function
      | None   -> fprintf ppf "None"
      | Some x -> fprintf ppf "Some %a" ppv x

    let atom ppf x = string ppf (StringStore.string x)
    let var ppf x = string ppf x

    let list sep = list ~pp_sep:(fun ppf () -> atom ppf sep)

    let rec pred ppf { name; infix; args } =
      match infix, args with
      |    _, [] -> fprintf ppf "%a" atom name
      | true,  _ -> fprintf ppf "%a" (list name term) args
      | _        -> fprintf ppf "%a(%a)" atom name (list_sep "," term) args
    and term ppf = function
      | Atom a -> atom ppf a
      | Var v  -> var ppf v
      | Pred p -> pred ppf p
      | Clause (p,s) -> fprintf ppf "%a :- %a" pred p term s

  end

  let rec term_vars l = function
    | Atom _ -> l
    | Var v  -> VarMap.add v v l
    | Pred p -> pred_vars l p
    | Clause (p,t) -> clause_vars l (p,t)
  and clause_vars l (p,t) =
    term_vars (pred_vars l p) t
  and pred_vars l p =
    List.fold_left term_vars l p.args


  let ground vars x = vars VarMap.empty x = VarMap.empty

  let term_ground = ground term_vars
  and clause_ground = ground clause_vars
  and pred_ground = ground pred_vars

end (* Ast *)

(* the database encoding of values is slightly different from the AST's.
 * Entries must be indexed by their corresponding atom and arity, and
 * they might either point to clauses or facts, the later being a clause
 * without a sequent (or with a tautological one). *)
module Reg = struct

  exception UndefinedValue

  open Ast

  type key = atom * int

  type clause = pred * arg option (* optional sequent *)

  type entry = clause list ref

  let mkkey = function
    | Clause ({ name;args },_)
    | Pred { name;args } -> Some (name, List.length args)
    | Atom s             -> Some (s, 0)
    | Var  _             -> None

  let mkvalue = function
    | Pred p       -> p,None
    | Clause (p,s) -> p,Some s
    | Atom name    -> Ast.{ name;infix=false;args=[] }, None
    | _            -> assert false

  type t = {
    clauses   : (key, entry) HT.t;
    operators : (atom, Ast.op * int) HT.t
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

  (* there are several kinds of operators:
   * f x
   * f y    (left associative)
   * x f
   * y f    (right associative)
   * x f x  (non associative)
   * x f y  (reduce on the right)
   * y f x  (reduce on the left)
   **)
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

    let key ppf (a,i) =
      fprintf ppf "(%a,%d)" Ast.PP.atom a i

    let value ppf = function
      | p, None   -> fprintf ppf "%a" Ast.PP.term (Pred p)
      | p, Some s -> fprintf ppf "%a" Ast.PP.term (Clause (p,s))

    let entry ppf k v =
      list ~pp_sep:(cut ";") value ppf !v

    let pp ppf reg =
      HT.iter (fun k v -> entry ppf k v) reg.clauses

  end

end (* Reg *)

module Parse = struct

  type buffer = {
    chan    : in_channel;
    parsing : bool;
    prompt  : bool -> unit;
    b       : Buffer.t;
    pos     : int;
    opened  : bool;
  }

  let mkbuff chan prompt =
    { chan; parsing = false; prompt; b = Buffer.create 211; pos = 0; opened = true }

  let fillbuff buff =
    if buff.pos >= Buffer.length buff.b && buff.opened
    then
      let rec fill buff =
        buff.prompt buff.parsing;
        let buff = { buff with parsing = true } in
        try
          match input_line buff.chan with
            "" -> fill buff
          | b  -> Buffer.add_string buff.b b;
                  buff
        with End_of_file -> { buff with opened = false }
      in
      fill buff
    else buff

  let updatebuff buff =
    dbg "clearbuff : %d %d@\n%!" (Buffer.length buff.b) buff.pos;
    let l = Buffer.length buff.b - buff.pos  in
    let s = Buffer.sub buff.b buff.pos l in
    let b = Buffer.create l in
    Buffer.add_string b s;
    { buff with b; pos = 0; parsing = false }

  let clearbuff buff =
    Buffer.clear buff.b;
    { buff with pos = 0; parsing = false }

  let pos buff = buff.pos

  let char buff =
    Buffer.nth buff.b buff.pos

  let next buff =
    { buff with pos = succ buff.pos }

  let lexeme buff start =
    dbg "lexeme : %d %d %d@\n%!" (Buffer.length buff.b) start buff.pos;
    let l = Buffer.sub buff.b start (buff.pos - start) in
    dbg "lexeme => %s@\n" l;
    l

  type token = [ `Dot | `Turnstile | `LPar | `RPar | `Op of string
               | `Var of string | `Atom of string ]

  let pp_token ppf = let open Fmt in function
    | `Dot       -> fprintf ppf "."
    | `Turnstile -> fprintf ppf ":-"
    | `LPar      -> fprintf ppf "("
    | `RPar      -> fprintf ppf ")"
    | `Op sym    -> fprintf ppf "OP %s" sym
    | `Var s     -> fprintf ppf "VAR %s" s
    | `Atom s    -> fprintf ppf "ATOM %s" s

  let var x = `Var x
  let atom x = `Atom x

  let turnstile x =
    if x = ":-" then `Turnstile else `Atom x


  type error =
      Eof
    | UnterminatedComment
    | MalformedTerm
    | MalformedPredicate
    | UnbalancedParentheses
    | UnexpectedToken of token
    | Other of exn

  let pp_error ppf =
    let fmt msg = Fmt.fprintf ppf msg in function
    | Eof                    -> fmt "unexpected end of stream" 
    | UnterminatedComment    -> fmt "unterminated comment"
    | MalformedTerm          -> fmt "malformed term"
    | MalformedPredicate     -> fmt "malformed predicate"
    | UnbalancedParentheses  -> fmt "unbalanced parentheses"
    | UnexpectedToken token  -> fmt "unexpected token '%a'" pp_token token
    | Other (Sys_error s)    -> fmt "system error : %s" s
    | Other _                -> fmt "unhandled error"

  type ('a,'b) cont = 'a -> buffer -> token -> 'b

  let next_token buff fail cont =
    try
      let buff = fillbuff buff in
      match buff.opened with
        false -> fail buff Eof
      | _     -> cont buff (char buff)
    with exn -> fail buff (Other exn)

  (* LEXER --- *)
  let token (type a) (cont : buffer -> token -> a) (fail : buffer -> error -> a) buff =
    let rec loop mk buff s =
      let fail buff = function
        | Eof -> cont buff @@ mk (lexeme buff s)
        | err -> fail buff err
      and cont buff = function
      | ','
      | ';'
      | '('
      | ')'
      | '.'
      | ':'
      | '='
      | ' ' -> cont buff @@ mk (lexeme buff s)
      | _   -> loop mk (next buff) s in
      next_token buff fail cont
    and loop_turnstile buff s =
     let fail buff = function
        | Eof -> cont buff @@ atom (lexeme buff s)
        | err -> fail buff err
     and cont buff = function
       | '-' -> let buff = next buff in cont buff @@ turnstile (lexeme buff s)
       | _   -> loop atom buff s in
      next_token buff fail cont
    and begin_comment buff s =
      let fail buff = function
        | Eof -> cont buff @@ atom (lexeme buff s)
        | err -> fail buff err
      and cont buff = function
        | '*' -> comment (next buff) (s + 2)
        | _   -> loop atom buff s in
      next_token buff fail cont
    and comment buff s =
      let fail buff _ = fail buff UnterminatedComment
      and cont buff = function
        | '*'      -> end_comment (next buff) (succ s)
        | _        -> comment (next buff) (succ s)
      in next_token buff fail cont
    and end_comment buff s =
      let fail buff _ = fail buff UnterminatedComment
      and cont buff = function
        | '/'      -> skip (next buff) (succ s)
        | '*'      -> end_comment (next buff) (succ s)
        | _        -> comment (next buff) (succ s)
      in next_token buff fail cont
    and skip buff s =
      let cont buff = function
        | ' '      -> skip (next buff) (succ s)
        | '/'      -> begin_comment (next buff) s
        | 'A'..'Z' -> loop var (next buff) s
        | '('      -> cont (next buff) `LPar
        | ')'      -> cont (next buff) `RPar
        | '.'      -> cont (next buff) `Dot 
        | '='      -> cont (next buff) @@ `Op StringStore.sequal
        | ','      -> cont (next buff) @@ `Op StringStore.scomma
        | ';'      -> cont (next buff) @@ `Op StringStore.ssemicolon
        | ':'      -> loop_turnstile (next buff) s
        | _        -> loop atom (next buff) s in
      next_token buff fail cont in
    skip buff (pos buff)

  open Ast

  (* PARSER --- *)

  (* handling operator precedence and associativity *)
  let reduce infix op1 op2 =
    dbg " { reduce %s %s }@\n%!" op1 op2;
    match infix op1, infix op2 with
    | Some l1 , Some l2 -> (snd l1) <= (snd l2)
    | Some _, None -> failwith "reduce operator 2"
    | _ -> failwith "reduce operator 1"

  let rec list parse (cont : ('a list,'b) cont) fail buff tk : 'b =
    parse (cont_list parse cont fail []) fail buff tk
  and cont_list parse cont fail (l : 'a list) (o : 'a) buff tk =
    match tk with
      `Op "," -> token (parse (cont_list parse cont fail (o::l)) fail) fail buff
    | _       -> cont (List.rev (o::l)) buff tk

  let rec term infix (cont : (term,'a) cont) fail buff tk : 'a =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "term @[<v>%!";
    match tk with
      `Var x  -> token (cont (Var x)) fail buff
    | `LPar   -> expr infix (op infix cont fail) fail buff tk
    | `Atom x -> token (begin_functor infix cont fail x) fail buff
    | `Op _     (* must be left unary *) 
    | _       -> fail buff MalformedTerm
  and begin_functor infix cont fail x buff = function
    | `LPar -> token (list (clause infix) (end_functor infix cont fail x) fail) fail buff
    | tk    -> cont (atom x) buff tk
  and end_functor infix (cont :  (term,'a) cont) fail name (args : term list) buff tk : 'a =
    match tk with
      `RPar -> token (cont (pred name args)) fail buff
    | _     -> fail buff MalformedPredicate

  (* handle infix notation *)
  and expr infix (cont : (term,'a) cont) fail buff tk =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "expr @[<v>%!";
    match tk with
    | `LPar -> token (expr infix (expr_parens infix cont fail) fail) fail buff
    | _     -> clause infix cont fail buff tk
  and op infix cont fail s buff tk =
    dbg "op : %a %a@\n" Ast.PP.term s pp_token tk;
    match tk with
      `Op sym    -> begin 
        (* 2 possibilities: unary right -> reduce | _ -> check precedence *)
        token (expr infix (op_rhs infix sym cont fail s) fail) fail buff
      end
    | _          -> cont s buff tk
  and op_rhs infix sym cont fail s1 s2 buff tk =
    let is_infix o =
      infix o != None in
    let pop s1 s2 = pred ~infix:(is_infix sym) sym [s1;s2] in
    dbg "op_rhs : %s %a %a %a" sym Ast.PP.term s1 Ast.PP.term s2 pp_token tk;
    match tk with
      `Op sym2 -> if reduce infix sym sym2
        then (op infix cont fail (pop s1 s2) buff tk)
        else token (expr infix (op_rhs infix sym2 (op_rhs infix sym cont fail s1) fail s2) fail) fail buff
    | _ -> cont (pop s1 s2) buff tk
  and expr_parens infix cont fail s buff tk =
    dbg "expr_parens@.";
    match tk with
    | `RPar -> token (cont s) fail buff
    | tk    -> fail buff UnbalancedParentheses

  and clause infix cont fail buff tk =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "clause @[<v>%!";
    term infix (clause_cont infix cont fail) fail buff tk
  and clause_cont infix cont fail (t : term) buff tk =
    match t, tk with
    | Pred p, `Turnstile -> token (expr infix (op infix (clause_end infix cont fail p) fail) fail) fail buff
    | _                  -> op infix cont fail t buff tk
  and clause_end infix cont fail p seq buff tk =
    cont (Ast.clause p seq) buff tk

  (* terms parser is used in the repl, clause parser is used in file loading *)
  let term infix cont fail buff =
    let cont t buff = function
      | `Dot -> cont buff t
      | tk   -> fail buff (UnexpectedToken tk) in
    token (term infix (op infix cont fail) fail) fail buff

  let clause infix cont fail buff =
    let cont t buff = function
      | `Dot -> cont buff t
      | tk   -> fail buff (UnexpectedToken tk) in
    token (clause infix cont fail) fail buff

end (* Parse *)

module Subst = struct

  type t = Ast.term Ast.VarMap.t

  let empty = Ast.VarMap.empty

  let is_empty (m : t) =
    Ast.VarMap.is_empty m

  let pp ppf (m : t) =
    let open Ast in let open Fmt in
    let l = VarMap.bindings m in
    let pp_pair ppf (v,t) = fprintf ppf "%a = %a" PP.var v PP.term t in
    fprintf ppf "%a" (list ~pp_sep:(cut ",") pp_pair) l

  let add v p s =
    Ast.VarMap.add v p s

  let find v s =
    Ast.VarMap.find v s

  let intersect vs s =
    let intersect k l r =
      match l, r with
        Some _, Some v -> Some v
      | _ -> None
    in
    Ast.VarMap.merge intersect vs s

  module Plain = struct

    let rec term_apply s t =
      let open Ast in
      match t with
      | Atom _       -> t
      | Var v        -> begin try find v s with Not_found -> t end
      | Pred p       -> Pred (pred_apply s p)
      | Clause (p,a) -> Clause (clause_apply s (p,a))
    and pred_apply s p =
      Ast.{ p with args = List.map (term_apply s) p.args }
    and clause_apply s ((p,a) : Ast.clause) =
      pred_apply s p, term_apply s a

    let subst_apply s1 s2 =
      Ast.VarMap.map (term_apply s1) s2

  end

  (* implementation promoting better sharing *)
  module Sharing = struct

    let opt_f f x = match f x with None -> x | Some x -> x

    let rec term_apply_opt s t =
      let opt_fg f g x = match f x with None -> None | Some x -> g x in
      let open Ast in
      match t with
      | Atom _       -> None
      | Var v        -> begin try Some (find v s) with Not_found -> None end
      | Pred p       -> opt_fg (pred_apply_opt s) (fun p -> Some (Pred p)) p
      | Clause c     -> opt_fg (clause_apply_opt s) (fun c -> Some (Clause c)) c
    and pred_apply_opt s p =
      let fld a (l,b) = match term_apply_opt s a with
          None -> (a::l,b)
        | Some t -> (t::l,true) in
      match List.fold_right fld p.Ast.args ([],false) with
      | _, false   -> None
      | args, true -> Some Ast.{ p with args }
    and clause_apply_opt s (p,a : Ast.clause) =
      match pred_apply_opt s p, term_apply_opt s a with
      | None, None     -> None
      | Some p, None   -> Some (p,a)
      | None, Some a   -> Some (p,a)
      | Some p, Some a -> Some (p,a)

    let subst_apply_opt s1 s2 =
    (* Map.map will always return a value physically
     * different from its input, thus we'll keep track
     * manually of whether [s2] remains unmodified
     * (note: Batteries might be a better fit here) *)
      let modified = ref false in
      let mapf =
        fun t -> match term_apply_opt s1 t with
          None -> t | Some t -> modified := true; t in
      let sa = Ast.VarMap.map mapf s2 in
      if !modified then Some sa else None

    let term_apply s1 = opt_f @@ term_apply_opt s1
    let pred_apply s1 = opt_f @@ pred_apply_opt s1
    let clause_apply s1 = opt_f @@ clause_apply_opt s1
    let subst_apply s1 = opt_f @@ subst_apply_opt s1

  end

  include Sharing

  let drop_tauto s =
    let open Ast in
    VarMap.filter (fun k -> function Var v when v = k -> false | _ -> true) s

  (* tries to compute the transitive closure of s,
   * ie, replaces variables in terms by the ground term
   * they associate with, if any *)
  let simplify s =
    let open Ast.VarMap in
    let merge_either k a b =
      match a, b with
        None, _ -> b
      | _, None -> a
      | _       -> assert false in
    let merge_include k a b =
      match a, b with
        None, _ -> b
      | _,    _ -> a in
    let rec loop gs s =
      (* find entries which are ground *)
      let gs', s' = partition (fun _ t -> Ast.term_ground t) s in
      dbg "simplify : %a -> @[gs = %a@; s = %a@]@."
        pp s pp gs' pp s';
      match is_empty gs' with
      | true  -> merge merge_either gs s
      | false -> match subst_apply_opt gs' s' with
        | None    -> merge merge_either gs s
        | Some s' -> loop (merge merge_include gs gs') s' in
    drop_tauto (loop empty s)

end (* Subst *)

module Unification = struct

  type subs = Subst.t

  open Ast

  let rec unify s left right =
    dbg "unify [%a] [%a]@." Ast.PP.term left Ast.PP.term right;
    match left, right with
      Atom a1, Atom a2 when a1 == a2 -> Some s
    | Var v1, Var v2  when v1 = v2   -> None
    | Var v1, Var v2                 -> unify_vars s v1 v2 left right
    | Var v, p
    | p, Var v                       -> unify_var_term s p v
    | Pred p1, Pred p2               -> unify_pred s p1 p2
    | _,_                            -> None
  and unify_pred s { name = n1; args = a1 } { name = n2; args = a2 } =
    let unify_opt = function
      | None -> fun _ _ -> None
      | Some s -> fun a b -> unify s a b in
    if n1 == n2 && List.length a1 = List.length a2
    then List.fold_left2 unify_opt (Some s) a1 a2
    else None
  and unify_vars s v1 v2 p1 p2 =
    let find v s =
      try Some (Subst.find v s)
      with Not_found -> None in
    match find v1 s, find v2 s with
      Some p1, Some p2 -> unify s p1 p2
    | Some p1, None    -> Some (Subst.add v2 p1 s)
    | None, Some p2    -> Some (Subst.add v1 p2 s)
    | None, None       -> Some (Subst.add v2 p1 s)
  and unify_var_term s p v =
    try unify s p (Subst.find v s)
    with Not_found -> Some (Subst.add v p s)

end (* Unification *)

(* evaluation: evaluation of a term shall return:
 * - the set of pairs of variables & terms which satisfies the term,
 * - true if that set is empty,
 * - or false if such set cannot be infered
 *)
module Eval = struct

  open Ast

  module Context = struct

    type t = {
      reg : Reg.t;
      sym : int;
    }

    let make () =
      { reg = Reg.make (); sym = 0 }

    let name n ctx =
      n^"_"^string_of_int ctx.sym, { ctx with sym = succ ctx.sym }

    let rec rename vars apply ctx t =
      let vm = vars VarMap.empty t in
      let r = ref ctx in
      let mapf (v : var) =
        let n, c = name v !r in
        r := c; (Var n) in
      let vm = VarMap.map mapf vm in
      !r, apply vm t

    let term_rename = rename Ast.term_vars Subst.term_apply
    and clause_rename = rename Ast.clause_vars Subst.clause_apply
    and pred_rename  = rename Ast.pred_vars Subst.pred_apply

    (* renaming of a reg entry *)
    let reg_rename ctx = function
      | p, None   -> let ctx, p = pred_rename ctx p in ctx, (p, None)
      | p, Some b -> let ctx, (p,b) = clause_rename ctx (p,b) in ctx, (p, Some b)

  end

  open Context

  (* fix-me: turn these into predicates *)
  exception UndefinedPredicate of Reg.key
  exception Uninstantiated
  exception TypeError of string
  exception StaticProcedure

  type 'a emit = Subst.t -> Context.t -> 'a
  type 'a fail = Subst.t -> Context.t -> 'a

  module Builtin = struct

    type ('a,'b) t =
      'a emit -> 'a fail -> Subst.t -> Context.t -> 'b list -> 'a

    module TblConf = struct

      type t = Reg.key

      let equal (k1,i1) (k2,i2) = k1 = k2 && i1 = i2

      let hash ((k,i) : t) =
        i * 211 + k

    end

    module Table = HT.Make(TblConf)

    let builtins : (unit,term) t Table.t = Table.create 211

    let add k v =
      Table.add builtins k v

    let find r =
      Table.find builtins r

  end

  let rec instantiate s = function
    | Atom _ as a  -> a
    | Var v  as a  -> begin
      try Subst.find v s
      with Not_found -> a
    end
    | Pred p       -> Pred (instantiate_pred s p)
    | Clause (p,a) -> Clause (instantiate_pred s p, instantiate s a)
  and instantiate_pred s { name;args;infix } =
    { name; args = List.map (instantiate s) args; infix }

  let as_predicate = function
    | Clause ({ name;args },_)
    | Pred { name;args } -> Some ((name, List.length args), args)
    | Atom s             -> Some ((s, 0), [])
    | Var  _             -> None

  type ('a,'b,'c) eval = 'a emit -> 'a fail -> Subst.t -> Context.t -> 'b -> 'c

  let ign _ _ = ()

  let rec conj : type b. ('a,b,'c) eval -> ('a,b list,'c) eval =
    fun eval emit fail s ctx -> function
    | []    -> emit s ctx
    | x::xs -> eval (fun s ctx -> conj eval emit fail s ctx xs) fail s ctx x

  let rec disj : type b. ('a,b,'c) eval -> ('a,b list,'c) eval =
    fun eval emit fail s ctx -> function
    | []    -> fail s ctx
    | x::xs -> eval emit ign s ctx x; disj eval emit fail s ctx xs

  (* evaluate a term by looking it up in the database:
   * this function ought to be tail recursive. Is it? *)
  let rec clause p emit fail s ctx c =
    let ctx, (p',a') = Context.reg_rename ctx c in
    dbg "Eval.clause [%a] [%a :- %a]@." Ast.PP.term p Ast.PP.pred p' Ast.PP.(opt term) a';
    dbg "subst : @[%a@]@." Subst.pp s;
    match Unification.unify s p (Pred p'), a' with
    | Some bindings, Some body -> term emit fail bindings ctx body
    | Some bindings, None      -> emit bindings ctx
    | None, _                  -> fail s ctx
  and term emit fail s ctx (p : term) =
    (* builtin predicates *)
    dbg "Eval.term [%a]@." Ast.PP.term p;
    match p with
    | Var v  -> raise Uninstantiated
    (* special builtins *)
    | Pred { name;args } when name == StringStore.semicolon -> disj term emit fail s ctx args
    | Pred { name;args } when name == StringStore.comma     -> conj term emit fail s ctx args
    | _ ->
       match as_predicate p with
       | None       -> assert false
       | Some (k,l) ->
          try (Builtin.find k) emit fail s ctx l
          with Not_found ->
            match Reg.find ctx.reg k with
            | Some e -> disj (clause (instantiate s p)) emit fail s ctx !e
            | None   -> raise (UndefinedPredicate k)

  exception Abort

  let rec continue () =
    let term_raw, term_cooked =
      let attr = Unix.(tcgetattr stdin) in
      (fun () -> Unix.(tcsetattr stdin TCSANOW { attr with c_icanon = false; c_echo = false })),
      (fun () -> Unix.(tcsetattr stdin TCSAFLUSH attr)) in
    try
      term_raw ();
      let c = input_char stdin in
      term_cooked ();
      match c with
        ';' | 'n' | ' ' | '\t' -> Fmt.eprintf ";@."
      | _ -> Fmt.eprintf ".@.%!"; raise Abort
    with End_of_file -> term_cooked (); exit 0


  (* top AST.term evaluation function:
   * should 'emit' every working set of variables instantiations
   * or fail if none is found *)
  let top ctx p =
    let vs = Ast.(term_vars VarMap.empty) p in
    let pp_result ppf s =
      match Subst.is_empty s with
        true -> Fmt.fprintf ppf "true%!"
      | _    -> Fmt.fprintf ppf "%a " Subst.pp s
    in
    let emit s reg =
      let s = Subst.simplify s in
      let s = Subst.intersect vs s in
      Fmt.eprintf "%a%!" pp_result s;
      continue ()
    and fail s reg = Fmt.eprintf "false.@.%!" in
    try term emit fail Subst.empty ctx p
    with Abort -> ()

end (* Eval *)

module Builtins = struct

  open Ast
  open Eval

  open Builtin

  let zero_arg f emit fail s ctx = function
    | [] -> f emit fail s ctx ()
    | _  -> assert false

  let one_arg f emit fail s ctx = function
    | [x] -> f emit fail s ctx x
    | _ -> assert false

  let two_args f emit fail s ctx = function
    | [x1;x2] -> f emit fail s ctx x1 x2
    | _ -> assert false

  let dummy_ = Eval.ign

  let true_ emit fail s ctx _ =
    emit s ctx

  let false_ emit fail s ctx _ =
    fail s ctx

  let ground emit fail s ctx t =
    match Ast.term_ground t with
      true -> emit s ctx
    | _    -> fail s ctx

  let var emit fail s ctx t =
    dbg "var@\n";
    dbg "subst : @[<v>%a@]@\n" Subst.pp s;
    match t with
    | Var v -> begin
      try match Subst.find v s with
      | Var _ -> true_ emit fail s ctx () | _ -> false_ emit fail s ctx ()
      with Not_found -> true_ emit fail s ctx ()
    end
    | _     -> false_ emit fail s ctx ()

  let assertx add emit fail s ctx p =
    match Reg.mkkey (instantiate s p) with
    | None   -> raise Uninstantiated
    | Some k ->
       dbg "assertx : @[term = %a@] [key = %a@]@." Ast.PP.term p Reg.PP.key k;
      try let _ = Builtin.find k in raise StaticProcedure
      with Not_found -> add ctx.Context.reg k p

  (* fix-me: implement listing/1 *)
  let listing_0 emit fail s ctx _ =
    Fmt.eprintf "%a@.%!" Reg.PP.pp ctx.Context.reg

  let halt emit fail s ctx =
    Fmt.eprintf "@.See you soon!@."; exit 0

  let unify emit fail s ctx a b =
    match Unification.unify s a b with
      Some bindings -> emit bindings ctx
    | None          -> fail s ctx

  let infix ctx o = Reg.Op.infix ctx.Context.reg (StringStore.atom o)
  let is_infix ctx o = Reg.Op.is_infix ctx.Context.reg (StringStore.atom o)

  (* consult loads a file by turning it into a buffer and
   * calling [assertx] above until error or EOF is reached.
   * fix-me: implement ':-'/1 *)
  let rec consult eval emit fail s ctx p =
    match instantiate s p with
    | Atom fname ->
       let open Parse in
       let fname = StringStore.string fname in
       let fname = if Filename.check_suffix fname ".pl"
         then fname
         else fname^".pl" in
       let chan = open_in fname in
       let fail buff = function
         | Eof -> buff
         | err -> Format.eprintf "syntax error (%d) : %a@." buff.pos pp_error err;
           buff
       and cont buff c =
         let buff = updatebuff buff in
         Fmt.eprintf "%a.@." Ast.PP.term c;
         assertx Reg.add_back emit fail s ctx c;
         buff in
       let rec loop buff =
         if buff.opened
         then loop (Parse.clause (infix ctx) cont fail buff) in
       loop (mkbuff chan (function _ -> ()))
    | _          -> raise Uninstantiated

end (* Builtins *)

module Init = struct

  open Builtins
  open Eval

  (* store a copy (in the heap) of the string in the string dictionary *)
  let string s = StringStore.atom @@ String.init (String.length s) (fun i -> s.[i])

  let builtin_defs = [
    (StringStore.true_,0),  (zero_arg true_);
    (StringStore.false_,0), (zero_arg false_);
    (string "listing", 0),  (zero_arg listing_0);
    (string "halt", 0),     (zero_arg halt);
    (string "ground",1),    (one_arg ground);
    (string "var", 1),      (one_arg var);
    (string "asserta",1),   (one_arg @@ assertx Reg.add_front);
    (string "assertz",1),   (one_arg @@ assertx Reg.add_back);
    (string "consult",1),   (one_arg @@ consult Eval.clause);
    (StringStore.equal,2),  (two_args unify);
  ]

  (* fix-me: should be in a prelude file *)
  let builtin_ops  = 
    let open Ast in [
    (StringStore.comma,     (Xfy,1000));
    (StringStore.semicolon, (Xfy,1100));
    (StringStore.turnstile, (Fx, 1200)); (* this is the unary turnstile used with consult/_ *)
    (StringStore.equal,     (Xfx, 700)); (* unification operator *)
  ]

  let init ctx =
    let iter_def (k,v) =
      dbg "Init def:%s@\n" (StringStore.string @@ fst k); 
      Builtin.add k v in
    List.iter iter_def builtin_defs;
    let iter_op (o,(k,l)) =
      dbg "Init op:%s@\n" (StringStore.string o); 
      Reg.Op.add ctx.Eval.Context.reg o k l in
    List.iter iter_op builtin_ops

end

type state = {
  ctx  : Eval.Context.t;
  buff : Parse.buffer
 }

let clearstate state =
  { state with buff = Parse.clearbuff state.buff }

let parse cont state =
  let open Parse in
  let fail buff =
    function
    | Eof -> Builtins.(halt dummy_ dummy_) Subst.empty state.ctx
    | err -> Fmt.eprintf "syntax error (%d): %a@." buff.pos pp_error err;
      clearstate { state with buff } in
  term (Builtins.infix state.ctx) cont fail state.buff

let eval_error ppf = let open Fmt in function
  | Eval.UndefinedPredicate (a,i) -> fprintf ppf "undefined predicate %s/%d" (StringStore.string a) i
  | Eval.Uninstantiated           -> fprintf ppf "unsufficiently instantiated value"
  | Eval.StaticProcedure          -> fprintf ppf "cannot modify a static value"
  | e -> raise e

let rec repl state =
  let cont = fun buff t ->
    let state = { state with buff = Parse.updatebuff buff } in
    try Eval.top state.ctx t; state
    with e ->
      Fmt.eprintf "evaluation error: %a@." eval_error e;
      clearstate state
  in
  let state = parse cont state in
  repl state

let top ctx =
  let prompt = function true -> Fmt.printf "| %!" | _ -> Fmt.printf "?- %!" in
  let state = { ctx; buff = Parse.mkbuff stdin prompt } in
  repl state

let load_file reg fname =
  let fname = StringStore.atom fname in
  ignore (Builtins.(consult dummy_ dummy_) Eval.clause Subst.empty reg (Ast.Atom fname))

open Arg

let load = ref []

let push_load s = load := s::!load

let usage s = s ^ ": [options] [files]"

let _ =
  Arg.parse (CmdLine.specs ()) push_load (usage Sys.argv.(0));
  let ctx = Eval.Context.make () in
  let () = Init.init ctx in
  let () =
    match !load with
      [] -> ()
    | l  -> List.iter (load_file ctx) @@ List.rev l
  in
  flush stderr;
  top ctx

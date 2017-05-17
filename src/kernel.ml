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
type var  = int * string

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

  module Arith = struct

    let sops = ["+"; "*"; "-"; "/"]
    let ops =  List.map atom sops

    let spreds = [ ">"; "<"; ">="; "=<"; "=:=" ]
    let preds = List.map atom spreds

  end

end

module ST = StringStore

module Ast = struct

  type term   = Atom of atom | Int of int | Var of var | Pred of pred | Clause of clause
  and  op     = Xfx | Xfy | Yfx | Fx | Fy | Xf | Yf
  and  pred   = { name : atom; infix : bool; args : arg list }
  and  arg    = term
  and  clause = pred * arg

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
      | _        -> fprintf ppf "%a(%a)" atom name (list_sep "," term) args
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

end (* Ast *)

(* the database encoding of values is slightly different from the AST's.
 * Entries must be indexed by their corresponding atom and arity, and
 * they might either point to clauses or predicates. *)
module Reg = struct

  exception UndefinedValue

  open Ast

  type key = atom * int

  type clause = pred * arg option (* optional sequent *)

  type entry = clause list ref

  let rec mkkey = function
    | Clause ({ name;args },_)
    | Pred { name;args } -> Some (name, List.length args)
    | Atom s             -> Some (s, 0)
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
    operators : (key, Ast.op * int) HT.t
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

    let key ppf (a,i) =
      fprintf ppf "%a/%d" Ast.PP.atom a i

    let value ppf = function
      | p, None   -> fprintf ppf "%a" Ast.PP.term (Pred p)
      | p, Some s -> fprintf ppf "%a" Ast.PP.term (Clause (p,s))

    let entry ppf (k,v) =
      list ~pp_sep:(cut ".") value ppf !v

    let pp ppf reg =
      HT.iter (fun k v -> fprintf ppf "%a.@." entry (k,v)) reg.clauses

  end

end (* Reg *)

module Parse = struct

  type buffer = {
    fname   : string;
    chan    : in_channel;
    parsing : bool;
    prompt  : bool -> unit;
    b       : Buffer.t;
    line    : int;
    col     : int;
    pos     : int;
    opened  : bool;
  }

  let mkbuff fname chan prompt =
    { fname; chan; parsing = false; prompt; b = Buffer.create 211; line = 0; col = 0; pos = 0; opened = true }

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
                  Buffer.add_string buff.b "\n";
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

  let newline buff = { buff with line = succ buff.line; col = 0 }

  let pos buff = buff.pos

  let char buff =
    Buffer.nth buff.b buff.pos

  let next buff =
    { buff with pos = succ buff.pos; col = succ buff.col }

  let lexeme buff start =
    dbg "lexeme : %d %d %d@\n%!" (Buffer.length buff.b) start buff.pos;
    let l = Buffer.sub buff.b start (buff.pos - start) in
    dbg "lexeme => %s@\n" l;
    l

  type token = [ `LPar | `RPar | `Op of string | `Dot
               | `Var of string | `Atom of string | `Scalar of string ]

  let pp_token ppf = let open Fmt in function
    | `Dot       -> fprintf ppf "."
    | `LPar      -> fprintf ppf "("
    | `RPar      -> fprintf ppf ")"
    | `Op sym    -> fprintf ppf "OP %s" sym
    | `Var s     -> fprintf ppf "VAR %s" s
    | `Atom s    -> fprintf ppf "ATOM %s" s
    | `Scalar s  -> fprintf ppf "SCALAR %s" s

  let var x = `Var x
  let atom x = `Atom x
  let operator x = `Op x
  let scalar x = `Scalar x

  let turnstile x =
    if x = ":-" then `Op (ST.sturnstile)  else `Op x

  type error =
      Eof
    | UnexpectedInput
    | UnterminatedComment
    | MalformedScalar
    | MalformedTerm
    | MalformedPredicate
    | UnbalancedParentheses
    | UnexpectedToken of token
    | UndefinedOperator of token
    | OperatorAssocMismatch
    | Other of exn

  let pp_error ppf =
    let fmt msg = Fmt.fprintf ppf msg in function
    | Eof                     -> fmt "unexpected end of stream"
    | UnexpectedInput         -> fmt "unexpected character"
    | UnterminatedComment     -> fmt "unterminated comment"
    | MalformedScalar         -> fmt "malformed scalar"
    | MalformedTerm           -> fmt "malformed term"
    | MalformedPredicate      -> fmt "malformed predicate"
    | UnbalancedParentheses   -> fmt "unbalanced parentheses"
    | UnexpectedToken token   -> fmt "unexpected token '%a'" pp_token token
    | UndefinedOperator token -> fmt "unknownn operator '%a'" pp_token token
    | OperatorAssocMismatch   -> fmt "operator associativity mismatch"
    | Other (Sys_error s)     -> fmt "system error : %s" s
    | Other e                 -> raise e

  type ('a,'b) cont = 'a -> buffer -> token -> 'b

  let next_token buff fail cont =
    try
      let buff = fillbuff buff in
      match buff.opened with
        false -> fail buff Eof
      | _     -> cont buff (char buff)
    with exn -> fail buff (Other exn)

  (* LEXER --- *)

  (* special characters : [ ] [\t] [,] [;] [(] [)] [']  *)

  let token (type a) (cont : buffer -> token -> a) (fail : buffer -> error -> a) buff =
    let efail mk s buff = function
      | Eof -> cont buff @@ mk (lexeme buff s)
      | err -> fail buff err
    and cfail buff _ = fail buff UnterminatedComment
    in
    let rec loop_op buff s =
      let cont buff = function
        | ':' | '&' | '=' | '#' | '|' | '\\'
        | '<' | '>' | '+' | '-' | '*' | '/'  -> loop_op (next buff) s
        | _ -> cont buff @@ operator (lexeme buff s) in
      next_token buff (efail operator s) cont
    and loop_alphanum mk buff s =
      let cont buff = function
        | 'A'..'Z' | 'a'..'z'
        | '0'..'9' | '_' | '-'  -> loop_alphanum mk (next buff) s
      | _   -> cont buff @@ mk (lexeme buff s)
      in next_token buff (efail mk s) cont
    and loop_num mk buff s =
      let cont buff = function
        | '.'  -> loop_decimals mk (next buff) s
        | '0'..'9' | '_'  -> loop_num mk (next buff) s
        | _   -> cont buff @@ mk (lexeme buff s)
      in next_token buff (efail mk s) cont
    and loop_decimals mk buff s =
      let cont buff = function
        | '0'..'9' | '_'  -> loop_decimals mk (next buff) s
        | _   -> cont buff @@ mk (lexeme buff s)
      in next_token buff (efail mk s) cont
    and begin_quoted mk buff s =
      let cont buff = function
        (* special case for double quote op *)
        | '\'' -> let buff = next buff in cont buff @@ operator (lexeme buff s)
        (* otherwise quoted atom/operator *)
        | _    -> quoted mk (next buff) (succ s)
      in next_token buff fail cont
    and quoted mk buff s =
      let cont buff = function
        (* we don't keep the quotes *)
        | '\'' -> cont (next buff) @@ mk (lexeme buff s)
        | _    -> quoted mk (next buff) s
      in next_token buff fail cont
    and begin_comment buff s =
      let cont buff = function
        | '*' -> comment (next buff) (s + 2)
        | _   -> loop_op buff s in
      next_token buff (efail atom s) cont
    and comment buff s =
      let cont buff = function
        | '*'      -> end_comment (next buff) (succ s)
        | _        -> comment (next buff) (succ s)
      in next_token buff cfail cont
    and end_comment buff s =
      let cont buff = function
        | '/'      -> skip (next buff) (succ s)
        | '*'      -> end_comment (next buff) (succ s)
        | _        -> comment (next buff) (succ s)
      in next_token buff cfail cont
    and dot buff s =
      let fail buff = function
        | Eof -> cont buff `Dot
        | err -> fail buff err
      and cont buff = function
        | ' ' | '\t' | '\n' | ','
        | ';' | '(' | ')' | '\'' -> dbg "lexeme => .@\n"; cont buff `Dot
        | _ -> loop_op (next buff) s
      in next_token buff fail cont
    and skip buff s =
      let cont buff = function
        (* spaces => skip to next char *)
        | '\n'           -> skip (next @@ newline buff) (succ s)
        | ' '   | '\t'   -> skip (next buff) (succ s)
        (* special chars *)
        | '('      -> dbg "lexeme => (@\n"; cont (next buff) `LPar
        | ')'      -> dbg "lexeme => )@\n"; cont (next buff) `RPar
        | ','      -> dbg "lexeme => ,@\n"; cont (next buff) @@ `Op ST.scomma
        | ';'      -> dbg "lexeme => ;@\n"; cont (next buff) @@ `Op ST.ssemicolon
        | '/'      -> begin_comment (next buff) s
        (* quoted atom *)
        | '\''     -> begin_quoted atom (next buff) s
        (* operators -- which characters are allowed? *)
        | '.'      -> dot (next buff) s
        | ':' | '&' | '=' | '#' | '|' | '\\'
        | '<' | '>' | '+' | '-' | '*' -> loop_op (next buff) s
        (* variables *)
        | 'A'..'Z' -> loop_alphanum var (next buff) s
        (* atoms *)
        | 'a'..'z' -> loop_alphanum atom (next buff) s
        (* scalars *)
        | '0'..'9' -> loop_num scalar (next buff) s
        | _        -> fail buff UnexpectedInput in
      next_token buff fail cont in
    skip buff (pos buff)

  open Ast

  (* PARSER --- *)

  let compare_assoc a1 a2 =
    match a1, a2 with
    | (Fx | Xfx | Yfx), (Yf | Yfx) ->  1 (* for equal precedence, x is reduced first *)
    | (Fy | Xfy), (Xf | Xfx | Xfy) -> -1
    | (Fy | Xfy), (Yf | Yfx)       ->  0
    | (Fx | Xfx | Yfx), (Xfx | Xfy | Xf) -> 0
    | (Xf | Yf), _ ->  1
    | _, (Fx | Fy) -> -1

  (* handling operator precedence and associativity *)
  let reduce infix op1 op2 =
    let pp_op ppf (a,b) = Fmt.fprintf ppf "%s/%d" a b in
    dbg " { reduce %a %a }@\n%!" pp_op op1 pp_op op2;
    match infix op1, infix op2 with
    | Some (a1,p1) , Some (a2,p2) ->
       begin
       match compare p1 p2, compare_assoc a1 a2 with
         0, 0 -> `FAIL
       | 0, k
       | k, _ -> if k < 0 then `REDUCE else `SHIFT
       end
    | Some _, None -> failwith "reduce operator 2"
    | _ -> failwith "reduce operator 1"


  let var x = Var (-1,x)

  (* fix-me: undefined operator could be a simple atom?*)
  (* note: within functors, comma's meaning changes *)

  let term infix cont fail buff =
    let rec term fnctr cont fail buff tk =
      let cont b x t =
        dbg "@]"; cont b x t in
      dbg "@[term %a@\n" pp_token tk;
      match tk with
      (* handle prefix ops *)
      | `Atom u
      | `Op u     -> begin
        match infix (u,1) with
        | Some ((Fx| Fy), _) -> token (term fnctr (op1_rhs fnctr u cont fail) fail) fail buff
        | tk                 -> token (begin_functor cont fail u) fail buff
      end
      | `Var x    -> token (cont (var x)) fail buff
      | `LPar     -> token (term false (op false (close_parens (op fnctr cont fail) fail) fail) fail) fail buff
      | `Scalar x -> begin
        try token (cont (Int (int_of_string x))) fail buff
        with Failure _ -> fail buff MalformedScalar
      end
      | _         -> fail buff MalformedTerm
    and op fnctr cont fail s buff tk =
      dbg "op : %b %a %a@\n" fnctr Ast.PP.term s pp_token tk;
      match tk with
      | `Atom sym
      | `Op sym    -> begin
        match sym, fnctr, infix (sym,2) with
        | ",", true, _  -> (* functor comma *)
           token (term fnctr (op2_reduce fnctr sym cont fail s) fail) fail buff
        | _,_,Some _ -> (* binary operator *) 
           token (term fnctr (op2_rhs fnctr sym cont fail s) fail) fail buff
        | _ -> (* else try unary *)
           match infix (sym,1) with
           | Some ((Xf|Yf), _) -> token (term fnctr (op1_reduce fnctr sym cont fail) fail) fail buff
           | Some ((Fx|Fy), _) -> fail buff MalformedTerm
           | _                 -> fail buff (UndefinedOperator tk)
      (* cont s buff tk *)
      end
      | _          -> cont s buff tk
    and op2_reduce fnctr sym cont fail s1 s2 buff tk =
      op fnctr cont fail (pred ~infix:true sym [s1;s2]) buff tk 
    and op1_reduce fnctr sym cont fail s1 buff tk =
      op fnctr cont fail (pred ~infix:false sym [s1]) buff tk 
    and op2_rhs fnctr sym cont fail s1 s2 buff tk =
      let pop2 s1 s2 = pred ~infix:true sym [s1;s2] in
      let reduce o2 rcont scont =
          match reduce infix (sym,2) o2 with
            `FAIL   -> fail buff OperatorAssocMismatch
          | `REDUCE -> rcont ()
          | `SHIFT  -> scont ()
      in
      dbg "op2_rhs : %s %a %a %a@\n" sym Ast.PP.term s1 Ast.PP.term s2 pp_token tk;
      match tk, fnctr with
      | `Op ",", true  -> cont (pop2 s1 s2) buff tk
      | (`Atom sym2 | `Op sym2), _    ->
         begin
           let scont1 () =
             token (op2_rhs fnctr sym cont fail s1 (pred sym2 [s2])) fail buff
           and scont2 () =
             token (term fnctr (op2_rhs fnctr sym2 (op2_rhs fnctr sym cont fail s1) fail s2) fail) fail buff
           and rcont () =
             token (term fnctr (op2_rhs fnctr sym2 cont fail (pop2 s1 s2)) fail) fail buff
           in
          match infix (sym2,2), infix (sym2,1) with
          | Some _, Some _  -> (* both exists: we should try first binary,
                                * and if no term follow downgrade to unary *)
             fail buff OperatorAssocMismatch
          | Some _, None    -> (* only binary *)
             reduce (sym2,2) rcont scont2
          | None, Some ((Xf|Yf),_) -> (* only unary postfix *)
             reduce (sym2,2) rcont scont1
          | None, Some ((Fx|Fy),_) -> (* only unary prefix *)
             fail buff OperatorAssocMismatch
          | _                      -> (* no such operator *)
             cont (pop2 s1 s2) buff tk
        end
      | _ -> cont (pop2 s1 s2) buff tk
    and op1_rhs fnctr (sym : string) cont fail s1 buff tk =
      let pop1 s = pred sym [s] in
      let reduce o2 rcont scont =
          match reduce infix (sym,1) o2 with
            `FAIL   -> fail buff OperatorAssocMismatch
          | `REDUCE -> rcont ()
          | `SHIFT  -> scont ()
      in
      dbg "op1_rhs : %s %a %a@\n" sym Ast.PP.term s1 pp_token tk;
      match tk with
      | `Op ","  when fnctr     -> cont (pop1 s1) buff tk
      | (`Atom sym2 | `Op sym2) ->
         begin
           let scont1 () =
             token (cont (pred sym [pred sym2 [s1]])) fail buff
           and scont2 () =
             token (term fnctr (op2_rhs fnctr sym2 (op1_rhs fnctr sym cont fail) fail s1) fail) fail buff
           and rcont () =
             token (term fnctr (op2_rhs fnctr sym cont fail (pred sym2 [s1])) fail) fail buff
           in
          match infix (sym2,2), infix (sym2,1) with
          | Some _, Some _  -> (* both exists: we should try first binary,
                                * and if no term follow downgrade to unary *)
             fail buff OperatorAssocMismatch
          | Some _, None    -> (* only binary *)
             reduce (sym2,2) rcont scont2
          | None, Some ((Xf|Yf),_) -> (* only unary postfix *)
             reduce (sym2,2) rcont scont1
          | None, Some ((Fx|Fy),_) -> (* only unary prefix *)
          fail buff OperatorAssocMismatch
          | _                      -> (* no such operator *)
             cont (pop1 s1) buff tk
        end
      | _ -> cont (pop1 s1) buff tk
    and begin_functor cont fail x buff tk =
      dbg "begin_functor %a@\n" pp_token tk;
      match tk with
      | `LPar -> token (term true (end_functor cont fail x []) fail) fail buff
      | _     -> cont (atom x) buff tk
    and end_functor (cont :  (term,'a) cont) fail name args a buff tk =
      dbg "end_functor %a@\n" pp_token tk;
      match tk with
      | `RPar   -> token (cont (pred name (List.rev @@ a::args))) fail buff
      | `Op "," -> token (term true (end_functor cont fail name (a::args)) fail) fail buff
      | `Atom _
      | `Op _   -> op true (end_functor cont fail name args) fail a buff tk
      | _       -> fail buff MalformedPredicate
    and close_parens cont fail s buff tk =
      dbg "expr_parens@\n";
      match tk with
      | `RPar -> token (cont s) fail buff
      | tk    -> fail buff UnbalancedParentheses
    in
    let cont t buff = function
      | `Dot -> cont buff t
      | tk   -> fail buff (UnexpectedToken tk) in
    token (term false (op false cont fail) fail) fail buff

end (* Parse *)

module Subst = struct

  type t = Ast.term Ast.VarMap.t

  let empty = Ast.VarMap.empty

  let is_empty (m : t) =
    Ast.VarMap.is_empty m

  let pp ppf (m : t) =
    Ast.PP.(varmap term) ppf m

  let add v p s =
    Ast.VarMap.add v p s

  let find v s =
    Ast.VarMap.find v s

  (* here [vs] is a 'a VarMap.t
   * we only mean to use it as set of var to filter [s] *)
  let intersect vs (s : t) : t =
    let intersect k l r =
      match l, r with
        Some _, Some _ -> r
      | _              -> None
    in
    Ast.VarMap.merge intersect vs s

  module Plain = struct

    let rec term_apply s t =
      let open Ast in
      match t with
      | Atom _       -> t
      | Int  _       -> t
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

    (* this function assumes that the substitution set [s]
     * is "disjoint", ie there are no dependencies betweeen
     *  substitutions in the set *)
    let rec term_apply_opt s t =
      let opt_fg f g x = match f x with None -> None | Some x -> g x in
      let open Ast in
      match t with
      | Atom _       -> None
      | Int _        -> None
      | Var v        -> begin try Some (find v s) with Not_found -> None end
      | Pred p       -> opt_fg (pred_apply_opt s) (fun p -> Some (Pred p)) p
      | Clause c     -> opt_fg (clause_apply_opt s) (fun c -> Some (Clause c)) c
    and pred_apply_opt s p =
      let fld a (l,b) = match term_apply_opt s a with
          None   -> (a::l,b)
        | Some t -> (t::l,true) in
      match List.fold_right fld p.Ast.args ([],false) with
      |    _, false -> None
      | args, true  -> Some Ast.{ p with args }
    and clause_apply_opt s (p,a : Ast.clause) =
      match pred_apply_opt s p, term_apply_opt s a with
      | None, None     -> None
      | Some p, None   -> Some (p,a)
      | None, Some a   -> Some (p,a)
      | Some p, Some a -> Some (p,a)

    let subst_apply_opt s1 s2 =
    (* Map.map will always return a value physically
     * different from its input, thus we'll keep track
     * manually of whether [s2] is equal to the result. *)
      let modified = ref false in
      let mapf =
        fun t -> match term_apply_opt s1 t with
          None -> t | Some t -> modified := true; t in
      let sa = Ast.VarMap.map mapf s2 in
      if !modified then Some sa else None

    let term_apply s1 = opt_f @@ term_apply_opt s1
    let pred_apply s1 = opt_f @@ pred_apply_opt s1
    let subst_apply s1 = opt_f @@ subst_apply_opt s1

  end

  include Sharing

  let drop_tauto s =
    let open Ast in
    VarMap.filter (fun k -> function Var v when v = k -> false | _ -> true) s

  (* we have a set of equations, we want to drop those that may be inlined,
   * ie. we want to try to eliminate variables which:
   * - are not defined in the original clause
   * - do not induce a recursion (ie, they are not present in both side of
   *   an equation).
   *)

  let intermediate (i,v) = i != -1

  let simplify s =
    let open Ast.VarMap in
    let rec loop s =
      (* find entries which are not cyclic *)
      let partf v t = not (Ast.term_bound v t) && intermediate v in
      let gs', s' = partition partf s in
      dbg "simplify: @[%a -> @[gs = @[{%a}@]@; s = @[{%a}@]@]@]@\n"
        pp s pp gs' pp s';
      (* are all remaining terms ground ?*)
      match is_empty gs' with
      | true  -> s' (* yes => we're done *)
      | false ->
         match subst_apply_opt gs' s with
         | None    -> s'
         | Some s' -> loop s' in
    drop_tauto (loop s)

end (* Subst *)

module Unification = struct

  type subs = Subst.t

  open Ast

  let rec unify s left right =
    dbg "unify [%a] [%a]@\n" Ast.PP.term left Ast.PP.term right;
    match left, right with
      Atom a1, Atom a2 when a1 == a2 -> Some s
    | Int i1, Int i2   when i1 = i2  -> Some s
    | Var v1, Var v2   when v1 = v2  -> None
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
    | Some p1, None    -> Some (add_subst v2 p1 s)
    | None, Some p2    -> Some (add_subst v1 p2 s)
    | None, None       -> match compare v1 v2 with
      | 0  -> None
      | -1 -> Some (Subst.add v1 p2 s)
      | _  -> Some (Subst.add v2 p1 s)
  and unify_var_term s p v =
    try unify s p (Subst.find v s)
    with Not_found -> Some (add_subst v p s)
  and add_subst v t s =
    (*    let t = Subst.term_apply s t in *)
    Subst.add v t s


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

    let name (i,n) ctx =
      (ctx.sym,n), { ctx with sym = succ ctx.sym }

    let rec rename vars apply ctx t =
      let vm = vars VarMap.empty t in
      let r = ref ctx in
      let mapf (v : var) =
        let n, c = name v !r in
        r := c; (Var n) in
      let vm = VarMap.map mapf vm in
      !r, apply vm t

    let term_rename = rename Ast.term_vars Subst.term_apply
    let pred_rename = rename Ast.pred_vars Subst.pred_apply
    let clause_rename ctx (a,b) =
      match term_rename ctx (Clause (a,b)) with
      | ctx, (Clause (a,b)) -> ctx, (a,b)
      | _ -> assert false

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
  exception StaticProcedure of Reg.key

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
    | Int _  as a  -> a
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
    | _                  -> None

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
    dbg "Eval.clause [%a] [%a :- %a]@\n" Ast.PP.term p Ast.PP.pred p' Ast.PP.(opt term) a';
    dbg "subst : @[%a@]@\n" Subst.pp s;
    match Unification.unify s p (Pred p'), a' with
    | Some bindings, Some body -> term emit fail bindings ctx (instantiate bindings body)
    | Some bindings, None      -> emit bindings ctx
    | None, _                  -> fail s ctx
  and term emit fail s ctx (p : term) =
    (* builtin predicates *)
    dbg "Eval.term [%a]@\n" Ast.PP.term p;
    match p with
    | Int _
    | Var _  -> raise Uninstantiated
    | Atom a -> let k = (a,0) in begin
      try (Builtin.find k) emit fail s ctx []
      with Not_found ->
        match Reg.find ctx.reg k with
        | Some e -> emit s ctx
        | None   -> raise (UndefinedPredicate k)
    end
    (* special builtins *)
    | Pred { name;args } when name == ST.semicolon -> disj term emit fail s ctx args
    | Pred { name;args } when name == ST.comma     -> conj term emit fail s ctx args
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

  let continue r =
    let term_raw, term_cooked =
      let attr = Unix.(tcgetattr stdin) in
      (fun () -> Unix.(tcsetattr stdin TCSANOW { attr with c_icanon = false; c_echo = false })),
      (fun () -> Unix.(tcsetattr stdin TCSAFLUSH attr)) in
    try
      term_raw ();
      let c = input_char stdin in
      term_cooked ();
      match c with
        ';' | 'n' | ' ' | '\t' -> ()
      | _ -> raise Abort
    with End_of_file -> term_cooked (); exit 0

  (* top AST.term evaluation function:
   * should 'emit' every working set of variables instantiations
   * or fail if none is found *)
  let top ctx p =
    (* [r] records whether we had at least one output *)
    let r = ref false in
    (* [vs] holds the variables of p *)
    let vs = Ast.(term_vars VarMap.empty) p in
    let pp_result ppf s =
      match Subst.is_empty s with
        true -> Fmt.fprintf ppf "true"
      | _    -> Fmt.fprintf ppf "%a " Subst.pp s
    in
    let emit s reg =
      if !r then Fmt.eprintf ";@.";
      dbg "@[<v 2>computing results:@;";
      dbg "@[var map: %a@]@\n" Ast.PP.(varmap var) vs;
      dbg "@[before simplification: %a@]@\n" pp_result s;
      let s = Subst.simplify s in
      dbg "@[before intersection: %a@]@\n" pp_result s;
      dbg "@]@.";
      let s = Subst.intersect vs s in
      Fmt.eprintf "%a%!" pp_result s;
      continue !r;
      r := true
    and fail s reg =
      if !r then Fmt.eprintf ";@.false%!"
      else Fmt.eprintf "false%!" in
    let _ =
      try term emit fail Subst.empty ctx p
      with Abort -> () in
    Fmt.eprintf ".@."

end (* Eval *)

module Builtins = struct

  open Ast
  open Eval

  open Builtin

  type term = Ast.term
  type ctx = Eval.Context.t

  let zero_arg f emit fail s ctx = function
    | [] -> f emit fail s ctx ()
    | _  -> assert false

  let one_arg f emit fail s ctx = function
    | [x] -> f emit fail s ctx x
    | _ -> assert false

  let two_args f emit fail s ctx = function
    | [x1;x2] -> f emit fail s ctx x1 x2
    | _ -> assert false

  let three_args f emit fail s ctx = function
    | [x1;x2;x3] -> f emit fail s ctx x1 x2 x3
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
       dbg "assertx : @[term = %a@] [key = %a]@]@.%!" Ast.PP.term p Reg.PP.key k;
      try let _ = Builtin.find k in raise (StaticProcedure k)
      with Not_found -> add ctx.Context.reg k p; true_ emit fail s ctx ()

  (* fix-me: implement listing/1 *)
  let listing_0 emit fail s ctx _ =
    Fmt.eprintf "%a@.%!" Reg.PP.pp ctx.Context.reg

  let halt emit fail s ctx =
    Fmt.eprintf "@.See you soon!@."; exit 0

  let unify emit fail s ctx a b =
    match Unification.unify s a b with
      Some bindings -> emit bindings ctx
    | None          -> fail s ctx

  let infix ctx (o,i) = Reg.Op.infix ctx.Context.reg (ST.atom o,i)
  let is_infix ctx (o,i) = Reg.Op.is_infix ctx.Context.reg (ST.atom o,i)

  (* consult loads a file by turning it into a buffer and
   * calling [assertx] above until error or EOF is reached.
   * fix-me: implement ':-'/1 *)
  let rec consult emit fail s ctx p =
    match instantiate s p with
    | Atom fname ->
       let open Parse in
       let fname = ST.string fname in
       let fname = if Filename.check_suffix fname ".pl"
         then fname
         else fname^".pl" in
       let chan = open_in fname in
       let rec cfail buff = function
         | Eof            -> true_ emit fail s ctx p
         | Other _ as err -> Format.eprintf "%a" pp_error err; false_ emit fail s ctx p
         | err            -> Format.eprintf "in '%s' at pos [%d,%d], %a@." buff.fname buff.line buff.col pp_error err;
                             false_ emit fail s ctx p
       and cont buff c =
         let buff = updatebuff buff in
         Fmt.eprintf "%a.@." Ast.PP.term c;
         (* assertx must remain silent *)
         assertx Reg.add_back dummy_ fail s ctx c;
         loop buff
       and loop buff =
         Parse.term (infix ctx) cont cfail buff in
       loop (mkbuff fname chan (function _ -> ()))
    | _          -> raise Uninstantiated


  module Arithmetic = struct

      open StringStore
      (* simple evaluation algorithm *)

      let [plus_;star_;minus_;div_] = Arith.ops

      let op a b = function
        | o when o = plus_   -> a + b
        | o when o = minus_  -> a - b
        | o when o = star_   -> a * b
        | o when o = div_    -> a / b
        | _ -> assert false

      let rec compute p =
        match p with
          Int i -> Int i
        | Pred { name; args = [l;r] } -> begin
          match compute l, compute r with
            Int i, Int j -> Int (op i j name)
          | _ -> assert false
        end
        | _ -> raise Uninstantiated

      let eval :  (int -> int -> bool) -> _ -> _ -> Subst.t -> ctx -> term -> term -> _ =
        fun op emit fail s ctx l r ->
        match compute l, compute r with
          Int i, Int j -> if op i j then emit s ctx else fail s ctx
        | _ -> assert false

      let preds =
        List.map (fun op emit fail s ctx l r -> eval op emit fail s ctx l r)
          [(>);(<);(=);(>=);(<=)]

  end

end (* Builtins *)

module Init = struct

  open Builtins

  (* store a copy (in the heap) of the string in the string dictionary *)
  let string s = ST.atom @@ String.init (String.length s) (fun i -> s.[i])

  let builtin_defs = [
    (ST.true_,0),  (zero_arg true_);
    (ST.false_,0), (zero_arg false_);
    (string "listing", 0),  (zero_arg listing_0);
    (string "halt", 0),     (zero_arg halt);
    (string "ground",1),    (one_arg ground);
    (string "var", 1),      (one_arg var);
    (string "asserta",1),   (one_arg @@ assertx Reg.add_front);
    (string "assertz",1),   (one_arg @@ assertx Reg.add_back);
    (string "consult",1),   (one_arg @@ consult);
    (ST.equal,2),  (two_args unify);
  ]

  let builtin_pred_defs =
    let ops = List.map (fun x -> two_args x) Builtins.Arithmetic.preds in
    Ast.(List.map2 (fun x y -> (x,2), y) StringStore.Arith.preds ops)

  (* fix-me: should be in a prelude file *)
  let builtin_ops  =
    let open Ast in [
    ((ST.comma,2),     (Xfy,1000));
    ((ST.semicolon,2), (Xfy,1100));
    ((ST.turnstile,2), (Xfx,1200));
    (*    (ST.turnstile, (Fx, 1200)); (* this is the unary turnstile used with consult/_ *) *)
    ((ST.equal,2),     (Xfx, 700)); (* unification operator *)
  ]

  let builtin_arith_ops = Ast.(Arithmetic.[
    (plus_,2),  (Yfx,500);
    (star_,2),  (Yfx,400);
    (minus_,2), (Yfx,500);
    (div_,2),   (Yfx,400);
  ])

  let builtin_preds = Ast.(List.map (fun x -> (x,2), (Xfx,700)) StringStore.Arith.preds)
(*
    ("=="); ("=\\="); ("is");
      (* ("@<"); ("@=<"); ("@>"); ("@>="); ("\="); ("\=="); ("as") *)
*)
  let init ctx =
    let iter_def (k,v) =
      dbg "Init def:%a@\n" Reg.PP.key k;
      Eval.Builtin.add k v in
    List.iter iter_def builtin_defs;
    List.iter iter_def builtin_pred_defs;
    let iter_op (o,(k,l)) =
      dbg "Init op:%a@\n" Reg.PP.key o;
      Reg.Op.add ctx.Eval.Context.reg o k l in
    List.iter iter_op (builtin_ops @ builtin_arith_ops @ builtin_preds)

end

type state = {
  ctx  : Eval.Context.t;
  buff : Parse.buffer
 }

let clearstate state =
  { state with buff = Parse.clearbuff state.buff }

let parse cont state =
  let open Parse in
  let fail buff = function
    | Eof -> Builtins.(halt dummy_ dummy_) Subst.empty state.ctx
    | err -> Fmt.eprintf "syntax error (%d): %a@." buff.pos pp_error err;
             clearstate { state with buff } in
  term (Builtins.infix state.ctx) cont fail state.buff

let eval_error ppf = let open Fmt in function
  | Eval.UndefinedPredicate k   -> fprintf ppf "undefined predicate %a" Reg.PP.key k
  | Eval.Uninstantiated         -> fprintf ppf "unsufficiently instantiated value"
  | Eval.StaticProcedure k      -> fprintf ppf "cannot modify static value %a" Reg.PP.key k
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
  let state = { ctx; buff = Parse.mkbuff "interactive" stdin prompt } in
  repl state

let load_file reg fname =
  let fname = ST.atom fname in
  ignore (Builtins.(consult dummy_ dummy_) Subst.empty reg (Ast.Atom fname))

open Arg

let load = ref []

let push_load s = load := s::!load

let usage s = s ^ ": [options] [files]"

let _ =
  Arg.parse (CmdLine.specs ()) push_load (usage Sys.argv.(0));
  let ctx = Eval.Context.make () in
  let () = Init.init ctx in
  let () =
    try
      match !load with
        [] -> ()
      | l  -> List.iter (load_file ctx) @@ List.rev l
    with e -> Fmt.eprintf "load error: %a@." eval_error e
  in
  flush stderr;
  top ctx

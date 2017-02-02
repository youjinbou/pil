
type atom = string
type var  = int

let debug_on = ref false

let dbg_true = fun msg -> Format.eprintf msg
let dbg_false = fun msg -> Format.(ifprintf err_formatter) msg

let dbg =
  if !debug_on then dbg_true else dbg_false

module Ast = struct

  type term   = Atom of string | Var of string | Pred of pred | Clause of clause

  and  pred   = { name : string; infix : bool; args : arg list }
  and  arg    = term
  and  clause = pred * arg

  type phrase = term

  (* string dictionary *)
  module Strings = Set.Make(struct type t = string let compare = compare end)

  let strings = ref Strings.empty

  let string x =
    try Strings.find x !strings
    with Not_found -> strings := Strings.add x !strings; x

  let atom x = Atom (string x)
  let var x = Var (string x)

  let pred ?(infix=false) name args = Pred { name = string name;infix;args }
  let clause x y = Clause (x,y)

  module VarMap = Map.Make(struct type t = string let compare = compare end)

  module PP = struct

    open Format

    let list sep = pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf sep)

    let opt ppv ppf = function
      | None   -> fprintf ppf "None"
      | Some x -> fprintf ppf "Some %a" ppv x

    let atom ppf = pp_print_string ppf
    let var ppf  = pp_print_string ppf

    let rec pred ppf { name; infix; args } =
      match infix, args with
      |    _, [] -> fprintf ppf "%s" name
      | true,  _ -> fprintf ppf "%a"  (list name term) args
      | _        -> fprintf ppf "%s(%a)" name (list "," term) args
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

module HT = Hashtbl

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
    | Atom s           -> Some (s, 0)
    | Var  _           -> None

  let mkvalue = function
    | Pred p       -> p,None
    | Clause (p,s) -> p,Some s
    | Atom name    -> Ast.{ name;infix=false;args=[] }, None
    | _            -> assert false

  type t = {
    clauses : (key, entry) HT.t
  }

  let make () = {
    clauses = HT.create 211;
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

  module PP = struct

    let value ppf = function
      | p, None   -> Format.fprintf ppf "%a\n" Ast.PP.term (Pred p)
      | p, Some s -> Format.fprintf ppf "%a\n" Ast.PP.term (Clause (p,s))

    let entry ppf k v =
      Ast.PP.list "\n" value ppf !v

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

  let dbg = dbg_false

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
    dbg "clearbuff : %d %d@.%!" (Buffer.length buff.b) buff.pos;
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
    dbg "lexeme : %d %d %d@.%!" (Buffer.length buff.b) start buff.pos;
    let l = Buffer.sub buff.b start (buff.pos - start) in
    dbg "lexeme => %s@." l;
    l

  type token = [ `Dot | `Turnstile | `LPar | `RPar | `Op of string
               | `Var of string | `Atom of string | `Eof ]

  let pp_token ppf = function
    | `Dot       -> Format.fprintf ppf "."
    | `Turnstile -> Format.fprintf ppf ":-"
    | `LPar      -> Format.fprintf ppf "("
    | `RPar      -> Format.fprintf ppf ")"
    | `Op sym    -> Format.fprintf ppf "%s" sym
    | `Var s     -> Format.fprintf ppf "%s" s
    | `Atom s    -> Format.fprintf ppf "%s" s
    | `Eof       -> Format.fprintf ppf "EOF"

  let var x = `Var x
  let atom x = `Atom x

  let turnstile x =
    if x = ":-" then `Turnstile else `Atom x

  exception SyntaxError of buffer * string
  exception Eof

  let syntax_error buff msg = raise @@ SyntaxError (buff,msg)

  let token buff : token * buffer =
    let rec loop mk buff s =
      let buff = fillbuff buff in
      match buff.opened with
        false -> mk (lexeme buff s), buff
      | _     -> match char buff with
                 | ','
                 | ';'
                 | '('
                 | ')'
                 | '.'
                 | ':'
                 | '='
                 | ' ' -> mk (lexeme buff s), buff
                 | _   -> loop mk (next buff) s
    and comment buff s =
      let buff = fillbuff buff in
      match buff.opened with
      | false -> syntax_error buff "unterminated comment"
      | _     -> match char buff with
                   '*'      -> end_comment (next buff) (succ s)
                 | _        -> comment (next buff) (succ s)
    and end_comment buff s =
      let buff = fillbuff buff in
      match buff.opened with
      | false -> syntax_error buff "unterminated comment"
      | _     -> match char buff with
                 | '/'      -> skip (next buff) (succ s)
                 | '*'      -> end_comment (next buff) (succ s)
                 | _        -> comment (next buff) (succ s)
    and skip buff s =
      let buff = fillbuff buff in
      match buff.opened with
      | false -> `Eof, buff
      | _     -> match char buff with
                 | ' '      -> skip (next buff) (succ s)
                 | '/'      -> begin
                   let buff = next buff in
                   match char buff with
                     '*' -> comment (next buff) (s + 2)
                   | _   -> loop atom buff s
                 end
                 | 'A'..'Z' -> loop var (next buff) s
                 | '('      -> `LPar, next buff
                 | ')'      -> `RPar, next buff
                 | '.'      -> `Dot , next buff
                 | '='      -> `Op "=", next buff
                 | ','      -> `Op ",", next buff
                 | ';'      -> `Op ";", next buff
                 | ':'      -> loop turnstile (next buff) s
                 | _        -> loop atom (next buff) s in
    skip buff (pos buff)

  type ('a,'b) cont = buffer -> 'a -> token -> 'b

  open Ast

  let rec list parse buff (cont : ('a list,'b) cont) tk : 'b =
    parse (cont_list parse cont []) buff tk
  and cont_list parse cont (l : 'a list) buff (o : 'a) tk =
    match tk with
      `Op "," -> let tk,buff = token buff in parse (cont_list parse cont (o::l)) buff tk
    | _       -> cont buff (List.rev (o::l)) tk

  let rec term (cont : (term,'a) cont) buff tk : 'a =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "term @[%!";
    match tk with
      `Var x  -> let tk, buff =  token buff in cont buff (Var x) tk
    | `LPar   -> expr cont buff tk
    | `Atom x -> begin
      match token buff with
      | `LPar, buff -> let tk, buff = token buff in list clause buff (end_functor cont x) tk
      | tk   , buff -> cont buff (atom x) tk
    end
    | _       -> syntax_error buff "malformed term"
  and end_functor (cont :  (term,'a) cont) name buff (args : term list) tk : 'a =
    match tk with
      `RPar -> let tk, buff = token buff in cont buff (pred name args) tk
    | _     -> syntax_error buff "malformed predicate"

  (* handle infix notation *)
  and expr (cont : (term,'a) cont) buff tk =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "expr @[%!";
    match tk with
    | `LPar -> let tk, buff = token buff in expr (expr_parens cont) buff tk
    | _     -> clause (op cont) buff tk
  and op cont buff s tk =
    match tk with
      `Op sym    -> let tk, buff = token buff in expr (op_rhs sym cont s) buff tk
    | _          -> cont buff s tk
  and op_rhs sym =
    let pop s1 s2 = pred sym [s1;s2] in
    fun cont s1 buff s2 tk ->
      cont buff (pop s1 s2) tk
  and expr_parens cont buff s = function
    | `RPar -> let tk, buff = token buff in cont buff s tk
    | tk    -> syntax_error buff "unbalanced parentheses"

  and clause cont buff tk =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "clause @[%!";
    term (clause_cont cont) buff tk
  and clause_cont cont buff (t : term) tk =
    match t, tk with
    | Pred p, `Turnstile -> let tk, buff = token buff in expr (clause_end cont p) buff tk
    | _                  -> cont buff t tk
  and clause_end cont p buff seq tk =
    cont buff (Ast.clause p seq) tk

  let fmt_syntax_error_token stg tk =
    Format.(fprintf str_formatter) "unexpected token '%a' at end of %s" pp_token tk stg;
    Format.flush_str_formatter ()

  (* terms parser is used in the repl, clause parser is used in file loading *)
  let term cont buff =
    let cont buff t = function
      | `Dot -> cont buff t
      | tk   -> let msg =  fmt_syntax_error_token "term" tk in
                raise @@ SyntaxError (buff,msg) in
    match token buff with
      `Eof, buff -> raise Eof
    | tk, buff   -> term cont buff tk

  let clause cont buff =
    let cont buff t = function
      | `Dot -> cont buff t
      | tk   -> let msg =  fmt_syntax_error_token "clause" tk in syntax_error buff msg in
    match token buff with
      `Eof, buff -> raise Eof
    | tk, buff   -> clause cont buff tk

end (* Parse *)

module Subst = struct

  type t = Ast.term Ast.VarMap.t

  let empty = Ast.VarMap.empty

  let is_empty (m : t) =
    Ast.VarMap.is_empty m

  let pp ppf (m : t) =
    let open Ast in
    let l = VarMap.bindings m in
    let pp_pair ppf (v,t) = Format.fprintf ppf "%a = %a" PP.var v PP.term t in
    Format.fprintf ppf "%a" (PP.list ",\n" pp_pair) l

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
    loop empty s

end (* Subst *)

module Unification = struct

  type subs = Subst.t

  open Ast

  let rec unify s left right =
    dbg "unify [%a] [%a]@." Ast.PP.term left Ast.PP.term right;
    match left, right with
      Atom a1, Atom a2 when a1 == a2 -> Some s
    | Var v1, Var v2  when v1 = v2   -> Some s
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
      n ^ "_" ^ (string_of_int ctx.sym), { ctx with sym = succ ctx.sym }

    let rec rename vars apply ctx t =
      let vm = vars VarMap.empty t in
      let r = ref ctx in
      let mapf v =
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

  module Builtin = struct

    type 'a emit = Subst.t -> Context.t -> 'a
    type 'a fail = Subst.t -> Context.t -> 'a

    type ('a,'b) t =
      'a emit -> 'a fail -> Subst.t -> Context.t -> 'b list -> 'a

    module TblConf = struct

      type t = Reg.key

      let equal (k1,i1) (k2,i2) = k1 == k2 && i1 = i2

      let hash (k,i) = Hashtbl.hash k + i

    end

    module Table = Hashtbl.Make(TblConf)

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
    | Atom s           -> Some ((s, 0), [])
    | Var  _           -> None

   (* evaluate a term by looking it up in the database:
    * this function ought to be tail recursive, is it? *)
  let rec term emit fail s ctx (p : term) =
    (* builtin predicates *)
    dbg "Eval.term %a@." Ast.PP.term p;
    match p with
    | Var v  -> raise Uninstantiated
    (* special builtins *)
    | Pred { name=";";args } -> disj emit fail s ctx args
    | Pred { name=",";args } -> conj emit fail s ctx args
    | _ ->
       match as_predicate p with
       | None       -> assert false
       | Some (k,l) ->
          try (Builtin.find k) emit fail s ctx l
          with Not_found ->
            match Reg.find ctx.reg k with
            | Some e -> reg_entry emit fail s ctx (instantiate s p) !e
            | None   -> raise (UndefinedPredicate k)
  and reg_entry emit fail s ctx p = function
    | [] -> assert false
    | cs -> List.iter (clause emit (fun _ _ -> ()) s ctx p) cs; fail s ctx
  and clause emit fail s ctx p c =
    let ctx, (p',a') = Context.reg_rename ctx c in
    dbg "Eval.clause [%a] [%a :- %a]@." Ast.PP.term p Ast.PP.pred p' Ast.PP.(opt term) a';
    dbg "s : @[%a@]@." Subst.pp s;
    match Unification.unify s p (Pred p'), a' with
    | Some bindings, Some body -> term emit fail bindings ctx body
    | Some bindings, None      -> emit bindings ctx
    | None, _                  -> fail s ctx
  and conj emit fail s ctx : term list -> unit = function
    | []    -> emit s ctx
    | x::xs -> term (fun s ctx -> conj emit fail s ctx xs) fail s ctx x
  and disj emit fail s ctx : term list -> unit = function
    | [] -> assert false
    | l  -> List.iter (term emit (fun _ _ -> ()) s ctx) l; fail s ctx

  exception Abort

  let rec continue () =
    let term_raw, term_cooked =
      let attr = Unix.(tcgetattr stdin) in
      (fun () -> Unix.(tcsetattr stdin TCSANOW { attr with c_icanon = false; c_echo = false })),
      (fun () -> Unix.(tcsetattr stdin TCSAFLUSH attr)) in
    term_raw ();
    let c = input_char stdin in
    term_cooked ();
    match c with
      ';' | 'n' | ' ' | '\t' -> Format.eprintf ";@."
    | _ -> Format.eprintf ".@.%!"; raise Abort

  (* top AST.term evaluation function:
   * should 'emit' every working set of variables instantiations
   * or fail if none is found *)
  let top ctx p =
    let vs = Ast.(term_vars VarMap.empty) p in
    let pp_result ppf s =
      let s = Subst.simplify s in
      let s = Subst.intersect vs s in
      match Subst.is_empty s with
        true -> Format.pp_print_string ppf "true."
      | _    -> Format.fprintf ppf "%a " Subst.pp s
    in
    let emit s reg =
      Format.eprintf "%a%!" pp_result s;
      continue ()
    and fail s reg = Format.eprintf "false.@.%!" in
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

  let dummy_ s ctx = ()

  let true_ emit fail s ctx _ =
    emit s ctx

  let false_ emit fail s ctx _ =
    fail s ctx

  let ground emit fail s ctx t =
    match Ast.term_ground t with
      true -> emit s ctx
    | _    -> fail s ctx

  let var emit fail s ctx t =
    match t with
    | Var _ -> emit s ctx
    | _     -> fail s ctx

  let assertx add emit fail s ctx p =
    match Reg.mkkey (instantiate s p) with
    | None   -> raise Uninstantiated
    | Some k ->
       try let _ = Builtin.find k in raise StaticProcedure
       with Not_found -> add ctx.Context.reg k p

  (* fix-me: implement listing/1 *)
  let listing emit fail s ctx _ =
    Format.eprintf "%a@.%!" Reg.PP.pp ctx.Context.reg

  let halt emit fail s ctx =
    Format.eprintf "@.See you soon!@."; exit 0

  let unify emit fail s ctx a b =
    match Unification.unify s a b with
      Some bindings -> emit bindings ctx
    | None          -> fail s ctx

  (* consult loads a file by turning it into a buffer and
   * calling [assertx] above until error or EOF is reached.
   * fix-me: implement ':-'/1 *)
  let rec consult eval emit fail s ctx p =
    match instantiate s p with
    | Atom fname ->
       let open Parse in
       begin
         try
           let fname = if Filename.check_suffix fname ".pl"
             then fname
             else fname^".pl" in
           let chan = open_in fname in
           let cont buff c =
             let buff = updatebuff buff in
             Format.eprintf "%a.@." Ast.PP.term c;
             assertx Reg.add_back emit fail s ctx c;
             buff in
           let rec loop buff =
             if buff.opened
             then loop (Parse.clause cont buff) in
           loop (mkbuff chan (function _ -> ()))
         with
         | SyntaxError (buff, msg) ->
            Format.eprintf "syntax error (%d): %s@." buff.pos msg
         | Eof -> ()
       end
    | _          -> raise Uninstantiated

end (* Builtins *)

module Init = struct

  open Builtins
  open Eval

  let string s = Ast.string @@ String.init (String.length s) (fun i -> s.[i])

  let builtin_defs : (Reg.key * (unit,Ast.term) Builtin.t) list = [
    (string "true",0),     (zero_arg true_);
    (string "false",0),    (zero_arg false_);
    (string "listing", 0), (zero_arg listing);
    (string "halt", 0),    (zero_arg halt);
    (string "ground",1),   (one_arg ground);
    (string "var", 1),     (one_arg var);
    (string "asserta",1),  (one_arg @@ assertx Reg.add_front);
    (string "assertz",1),  (one_arg @@ assertx Reg.add_back);
    (string "consult",1),  (one_arg @@ consult Eval.clause);
  ]

  let _ =
    let iterf (k,v) = dbg "Init:%s@." (fst k); Builtin.add k v in
    List.iter iterf builtin_defs

end

type state = {
  ctx  : Eval.Context.t;
  buff : Parse.buffer
 }

let clearstate state =
  { state with buff = Parse.clearbuff state.buff }

let parse cont state =
  let open Parse in
  try term cont state.buff
  with
  | SyntaxError (buff, msg) ->
     Format.eprintf "syntax error (%d): %s@." buff.pos msg; clearstate { state with buff }
  | Eof -> Builtins.(halt dummy_ dummy_) Subst.empty state.ctx

let eval_error ppf = let open Format in function
  | Eval.UndefinedPredicate (a,i) -> fprintf ppf "undefined predicate %s/%d" a i
  | Eval.Uninstantiated           -> fprintf ppf "unsufficiently instantiated value"
  | Eval.StaticProcedure          -> fprintf ppf "cannot modify a static value"
  | e -> raise e

let rec repl state =
  let cont = fun buff t ->
    let state = { state with buff = Parse.updatebuff buff } in
    try Eval.top state.ctx t; state
    with e ->
      Format.eprintf "evaluation error: %a@." eval_error e;
      clearstate state
  in
  let state = parse cont state in
  repl state

let top ctx =
  let prompt = function true -> Format.printf "| %!" | _ -> Format.printf "?- %!" in
  let state = { ctx; buff = Parse.mkbuff stdin prompt } in
  repl state

let load_file reg fname =
  ignore (Builtins.(consult dummy_ dummy_) Eval.clause Subst.empty reg (Ast.Atom fname))

let _ =
  let ctx = Eval.Context.make () in
  match Sys.argv with
    [| _ |] -> top ctx
  | _       ->
     for i = 1 to pred @@ Array.length Sys.argv do
       load_file ctx Sys.argv.(i)
     done;
    top ctx

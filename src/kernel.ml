open PList

module HT = Hashtbl

let dbg = Debug.printf

module ST = StringStore

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
    let flt k = function Var v when is_instance v -> false | _ -> true in
    VarMap.filter flt s

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
  exception DomainError of string

  type 'a emit = Subst.t -> Context.t -> 'a
  type 'a fail = Subst.t -> Context.t -> 'a

  module Builtin = struct

    type ('a,'b) t =
      'a emit -> 'a fail -> Subst.t -> Context.t -> 'b list -> 'a

    module TblConf = struct

      type t = Reg.key
      let equal k1 k2 = Reg.Key.compare k1 k2 = 0
      let hash = Reg.Key.hash

    end

    module Table = HT.Make(TblConf)

    let builtins : (unit,term) t Table.t = Table.create 211

    let add k v =
      Table.add builtins k v

    let find r =
      Table.find builtins r

  end

  let op_kind = let open OpKind in let open ST.OpKinds in function
    | x when x == xfx -> Xfx | x when x == xfy -> Xfy | x when x == yfx -> Yfx
    | x when x == fx -> Fx | x when x == fy -> Fy | x when x == xf -> Xf | x when x == yf -> Yf
    | _ -> raise (DomainError "operator kind")

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

  let as_predicate t =
    match t with
    | Clause ({ name;args },_)
    | Pred { name;args } -> begin
      match Reg.mkkey t with
      | Some k -> Some (k, args)
      | None   -> None (* assert false *)
    end
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
    | Atom a -> let k = Reg.(key_of_atom default_context a) in begin
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

  let infix ctx o i = Reg.(Op.infix ctx.Context.reg (key_of_operator default_context (ST.atom o) i))

  let is_infix ctx o i = Reg.(Op.is_infix ctx.Context.reg (key_of_operator default_context (ST.atom o) i))

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
         | Other _ as err -> Format.eprintf "%a@." pp_error err; false_ emit fail s ctx p
         | err            -> Format.eprintf "in '%s' at pos [%d,%d], %a@."
                               buff.fname buff.line buff.col pp_error err;
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

    let (C (plus_, C (star_, C (minus_, C (div_,N))))) = Arith.ops

    let op a b = function
      | o when o == plus_   -> a + b
      | o when o == minus_  -> a - b
      | o when o == star_   -> a * b
      | o when o == div_    -> a / b
      | _ -> assert false

    let rec compute p =
      match p with
        Int i -> Int i
      | Pred { name; args = [l;r] } -> begin
        match compute l, compute r with
          Int i, Int j -> Int (op i j name)
        | _ -> raise (TypeError "non computable value")
      end
      | _ -> raise (TypeError "non computable value")

    let eval :  (int -> int -> bool) -> _ -> _ -> Subst.t -> ctx -> term -> term -> _ =
      fun op emit fail s ctx l r ->
        match compute l, compute r with
          Int i, Int j -> if op i j then emit s ctx else fail s ctx
        | _ -> assert false

    let preds =
      PList.map (fun op emit fail s ctx l r -> eval op emit fail s ctx l r)
        ((>) @& (<) @& (=) @& (>=) @& (<=) @& N)

  end

  let is_ emit fail s ctx l r =
    match l, Arithmetic.compute r with
      Int i, Int j when i = j -> true_ emit fail s ctx ()
    | _                       -> false_ emit fail s ctx ()

  let op_ emit fail s ctx p t n =
    match instantiate s p, instantiate s t, instantiate s n with
    | Int p, Atom t, Atom o -> begin
       let kind = op_kind t in
       let key = Reg.(key_of_operator default_context o @@ OpKind.arity kind) in
       match o with
       | x when x = ST.comma || x = ST.nil || (x = ST.pipe && p < 1001) -> raise (StaticProcedure key)
       | _ -> Reg.(Op.add ctx.Eval.Context.reg key kind p);
      true_ emit fail s ctx ()
    end
    | _ -> raise Uninstantiated

  let defined_ops emit fail s ctx () =
    Reg.display_ops ctx.Context.reg

end (* Builtins *)

module Init = struct

  open Builtins

  (* store a copy (in the heap) of the string in the string dictionary *)
  let string s = ST.atom @@ String.init (String.length s) (fun i -> s.[i])

  let builtin_defs = [
    (ST.true_,0),            (zero_arg true_);
    (ST.false_,0),           (zero_arg false_);
    (string "listing", 0),   (zero_arg listing_0);
    (string "halt", 0),      (zero_arg halt);
    (string "ground",1),     (one_arg ground);
    (string "var", 1),       (one_arg var);
    (string "asserta",1),    (one_arg @@ assertx Reg.add_front);
    (string "assertz",1),    (one_arg @@ assertx Reg.add_back);
    (string "consult",1),    (one_arg @@ consult);
    (ST.equal,2),            (two_args unify);
    (ST.is, 2),              (two_args is_);
    (ST.op, 3),              (three_args op_);
    (string "ops",0),        (zero_arg defined_ops);
  ]

  let builtin_pred_defs =
    let ops = PList.map (fun x -> two_args x) Builtins.Arithmetic.preds in
    Ast.(PList.map2 (fun x y -> (x,2), y) StringStore.Arith.preds ops)

  (* fix-me: should be in a prelude file *)
  let builtin_ops  =
    OpKind.(
      ((ST.comma,2),     (Xfy,1000)) @&
      ((ST.semicolon,2), (Xfy,1100)) @&
      ((ST.pipe,2),      (Xfy,1100)) @&
      ((ST.turnstile,2), (Xfx,1200)) @&
      (*    ((ST.turnstile,1), (Fx, 1200)) @& (* this is the unary turnstile used with consult/_ *) *)
      ((ST.equal,2),     (Xfx, 700)) @& (* unification operator *)
      ((ST.is,2),        (Xfx, 700)) @& N
    )

  let builtin_arith_ops = OpKind.(Arithmetic.(
    ((plus_,2),  (Yfx,500)) @&
    ((star_,2),  (Yfx,400)) @&
    ((minus_,2), (Yfx,500)) @&
    ((div_,2),   (Yfx,400)) @& N
  ))

  let builtin_preds = OpKind.(PList.map (fun x -> (x,2), (Xfx,700)) StringStore.Arith.preds)
 (* ("=="); ("=\\="); *)
 (* ("@<"); ("@=<"); ("@>"); ("@>="); ("\="); ("\=="); ("as") *)

  let init ctx =
    let iter_def ((a,i),v) =
      let k = Reg.(Key.make default_context a i) in
      dbg "Init def:%a@\n" Reg.PP.key k;
      Eval.Builtin.add k v in
    List.iter iter_def builtin_defs;
    PList.iter iter_def builtin_pred_defs;
    let iter_op ((a,i),(k,l)) =
      let o = Reg.(key_of_operator default_context a i) in
      dbg "Init op:%a@\n" Reg.PP.key o;
      Reg.Op.add ctx.Eval.Context.reg o k l in
    (* no type level concat *)
    PList.iter iter_op builtin_ops;
    PList.iter iter_op builtin_arith_ops;
    PList.iter iter_op builtin_preds

end

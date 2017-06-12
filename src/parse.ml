module ST = StringStore

let dbg = Debug.printf

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
  { fname; chan; parsing = false; prompt; b = Buffer.create 211;
    line = 0; col = 0; pos = 0; opened = true }

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

let prev buff =
  { buff with pos = pred buff.pos; col = pred buff.col }

let next buff =
  { buff with pos = succ buff.pos; col = succ buff.col }

let lexeme buff start =
  dbg "lexeme : %d %d %d@\n%!" (Buffer.length buff.b) start buff.pos;
  let l = Buffer.sub buff.b start (buff.pos - start) in
  dbg "lexeme => %s@\n" l;
  l

type token = [ `LPar | `RPar | `LBra | `RBra | `Op of string | `Dot
             | `Var of string | `Atom of string | `Scalar of string ]

let pp_token ppf = let open Fmt in function
  | `Dot       -> fprintf ppf "."
  | `LPar      -> fprintf ppf "("
  | `RPar      -> fprintf ppf ")"
  | `LBra      -> fprintf ppf "["
  | `RBra      -> fprintf ppf "]"
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

(* special characters : [ ] [\t] [,] [;] [(] [)] ['] [[] [|] []] *)

let token (type a) (cont : buffer -> token -> a) (fail : buffer -> error -> a) buff =
  let efail mk s buff = function
    | Eof -> cont buff @@ mk (lexeme buff s)
    | err -> fail buff err
  and cfail buff _ =
    fail buff UnterminatedComment
  in
  let rec loop_op buff s =
    let cont buff = function
      | ':' | '&' | '=' | '#' | '|' | '\\'
      | '<' | '>' | '+' | '-' | '*' | '/'
      | '[' | ']' -> loop_op (next buff) s
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
      | '.'  -> loop_dot_decimals mk (next buff) s
      | '0'..'9' | '_'  -> loop_num mk (next buff) s
      | _   -> cont buff @@ mk (lexeme buff s)
    in next_token buff (efail mk s) cont
  and loop_dot_decimals mk buff s =
    let cont buff = function
      | '0'..'9' | '_'  -> loop_decimals mk (next buff) s
      | _   -> let b = prev buff in cont b @@ mk (lexeme b s)
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
      | '['      -> dbg "lexeme => [@\n"; cont (next buff) `LBra
      | ']'      -> dbg "lexeme => ]@\n"; cont (next buff) `RBra
      | '|'      -> dbg "lexeme => |@\n"; cont (next buff) @@ `Op ST.spipe
      | '/'      -> begin_comment (next buff) s  (* potentially an operator *)
      (* quoted atom *)
      | '\''     -> begin_quoted atom (next buff) s
      (* operators -- which characters are allowed? *)
      | '.'      -> dot (next buff) s
      | ':' | '&' | '=' | '#' | '\\'
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
open OpKind

let compare_assoc a1 a2 =
  match a1, a2 with
  | (Fx | Xfx | Yfx), (Yf | Yfx) -> -1 (* for equal precedence, x is reduced first *)
  | (Fy | Xfy), (Xf | Xfx | Xfy) ->  1
  | (Fy | Xfy), (Yf | Yfx)       ->  0
  | (Fx | Xfx | Yfx), (Xfx | Xfy | Xf) -> 0
  | (Xf | Yf), _ ->  1
  | _, (Fx | Fy) -> -1

(* this indicate the parser state wrt comma's meaning.
 * at this point, comma's behaviour is hardwired in
 * the parser; however, would it be possible to modulate
 * the result of the 'infix' function according to the state
 * below and simplify the parser code? Perhaps the op/3 
 * predicate could also be extended to add new behaviours?
 * (module implementation?) *)
type state = [ `NONE | `CONS | `OTHER ]

let str_state = function
  | `NONE  -> "NONE"
  | `CONS  -> "CONS"
  | `OTHER -> "OTHER"

(* handling operator precedence and associativity *)
let reduce (a1,p1) (a2,p2) =
  match compare p1 p2, compare_assoc a1 a2 with
    0, 0 -> dbg "reduce: 0@\n%!"; `FAIL
  | 0, k
  | k, _ -> dbg "reduce: (%d,%d) => %d@\n%!" p1 p2 k; if k < 0 then `REDUCE else `SHIFT

let reduce_opt op1 op2 =
  match op1, op2 with
  | Some o1, Some o2 -> reduce o1 o2
  | Some _, None -> failwith "reduce operator 2"
  | _ -> failwith "reduce operator 1"

let var x = Var (-1,x)

(* replace "right-recursively":
 * - commas by list cons
 * - pipes by list tails
 * it's tricky, because of the way the parser works
 *)
let list p =
  dbg "list : %a@." Ast.PP.term p;
  let rec list = function
    | Pred { name; infix; args = [hd;tl] } when name = ST.comma -> begin
      match tl with
      | Pred { name = tname; infix = tinfix; args = targs } when tname = ST.cons ->
         Pred { name = ST.cons; infix; args = [hd; tl] }
      | _ -> Pred { name = ST.cons; infix; args = [hd; list tl] }
    end
    | Pred {name; infix; args} when name = ST.pipe ->
       Pred { name = ST.cons; infix; args }
    | x -> Pred {name = ST.cons; infix=true ; args = [x;Atom ST.nil ] }
  in list p

let term infix cont fail buff =
  let rec term state cont fail buff tk =
    let cont b x t =
      dbg "@]"; cont b x t in
    dbg "@[term %a@\n" pp_token tk;
    match tk with
    (* handle prefix ops *)
    | `Atom u
    | `Op u     ->
       begin
      match infix u 1 with
      | Some ((Fx| Fy), _) -> token (term state (op1_rhs state u cont fail) fail) fail buff
      | Some _             -> fail buff OperatorAssocMismatch
      | None               -> token (begin_functor cont fail u) fail buff
    end
    | `Var x    -> token (cont (var x)) fail buff
    | `LPar     -> token (term `NONE (close_parens cont fail) fail) fail buff
    | `LBra     -> token (term `CONS (close_bracket cont fail) fail) fail buff
    | `Scalar x -> begin
      try token (cont (Int (int_of_string x))) fail buff
      with Failure _ -> fail buff MalformedScalar
    end
    | _         -> fail buff MalformedTerm
  and op state cont fail s buff tk =
    match tk with
    | `Atom sym
    | `Op sym    -> begin
      match sym, state, infix sym 2 with
      | "|", `CONS, _ -> (* replace operator in list state *)
         token (term state (op2_rhs state ST.scons cont fail s) fail) fail buff
      | ",", `OTHER, _  -> (* functor comma *)
         cont s buff tk
      | _, _, Some _ -> (* binary operator *) 
         token (term state (op2_rhs state sym cont fail s) fail) fail buff
      | _ -> (* else try unary *)
         match infix sym 1 with
         | Some ((Xf|Yf), _) -> token (term state (op1_reduce state sym cont fail) fail) fail buff
         | Some ((Fx|Fy), _) -> fail buff MalformedTerm
         | _                 -> fail buff (UndefinedOperator tk)
    end
    | _          -> cont s buff tk
  and op2_reduce state sym cont fail s1 s2 buff tk =
    op state cont fail (pred ~infix:true sym [s1;s2]) buff tk
  and op1_reduce state sym cont fail s1 buff tk =
    op state cont fail (pred ~infix:false sym [s1]) buff tk
  and op2_rhs state sym cont fail s1 s2 buff tk =
    let pop2 s1 s2 = pred ~infix:true sym [s1;s2] in
    let reduce o2 a2 rcont scont =
      match reduce_opt (infix sym 2) (infix o2 a2) with
        `FAIL   -> fail buff OperatorAssocMismatch
      | `REDUCE -> rcont ()
      | `SHIFT  -> scont ()
    in
    dbg "op2_rhs : %s %s <%a> <%a> %a@\n" (str_state state) sym Ast.PP.term s1 Ast.PP.term s2 pp_token tk;
    match tk, state with
    | `Op ",", `OTHER -> cont (pop2 s1 s2) buff tk
    | `Op "|", `CONS when sym = ST.scomma -> token (term state (op2_rhs state ST.scons (op2_reduce state sym cont fail s1) fail s2) fail) fail buff
    | `Op ",", `CONS when sym = ST.scons  -> fail buff MalformedTerm
    | (`Atom sym2 | `Op sym2), _          ->
       begin
         let scont1 () =
           token (op2_rhs state sym cont fail s1 (pred sym2 [s2])) fail buff
         and scont2 () =
           token (term state (op2_rhs state sym2 (op2_rhs state sym cont fail s1) fail s2) fail) fail buff
         and rcont () =
           token (term state (op2_rhs state sym2 cont fail (pop2 s1 s2)) fail) fail buff
         in
        match infix sym2 2, infix sym2 1 with
        | Some _, Some _  -> (* both exists: we should try first binary,
                              * and if no term follows downgrade to unary *)
           fail buff OperatorAssocMismatch
        | Some _, None    -> (* only binary *)
           reduce sym2 2 rcont scont2
        | None, Some ((Xf|Yf),_) -> (* only unary postfix *)
           reduce sym2 2 rcont scont1
        | None, Some ((Fx|Fy),_) -> (* only unary prefix *)
           fail buff MalformedTerm
        | _                      -> (* no such operator *)
           cont (pop2 s1 s2) buff tk
       end
    | _ -> cont (pop2 s1 s2) buff tk
  and op1_rhs state (sym : string) cont fail s1 buff tk =
    let pop1 s = pred sym [s] in
    let reduce o2 a2 rcont scont =
      match reduce_opt (infix sym 1) (infix o2 a2) with
        `FAIL   -> fail buff OperatorAssocMismatch
      | `REDUCE -> rcont ()
      | `SHIFT  -> scont ()
    in
    dbg "op1_rhs : %s %a %a@\n" sym Ast.PP.term s1 pp_token tk;
    match tk, state with
    | `Op ",", `OTHER -> cont (pop1 s1) buff tk (* reduce *)
    | `Op ",", `CONS  -> cont (pop1 s1) buff tk (* reduce *)
    | `Op "|", `CONS  -> token (term state (op2_rhs state ST.scons (op1_reduce state sym cont fail) fail s1) fail) fail buff
    | (`Atom sym2 | `Op sym2), _ ->
       begin
         let scont1 () =
           token (cont (pred sym [pred sym2 [s1]])) fail buff
         and scont2 () =
           token (term state (op2_rhs state sym2 (op1_rhs state sym cont fail) fail s1) fail) fail buff
         and rcont () =
           cont (pop1 s1) buff tk
         in
        match infix sym2 2, infix sym2 1 with
        | Some _, Some _  -> (* both exists: we should try first binary,
                              * and if no term follow downgrade to unary *)
           fail buff OperatorAssocMismatch
        | Some _, None    -> (* only binary *)
           reduce sym2 2 rcont scont2
        | None, Some ((Xf|Yf),_) -> (* only unary postfix *)
           reduce sym2 2 rcont scont1
        | None, Some ((Fx|Fy),_) -> (* only unary prefix *)
           fail buff MalformedTerm
        | _                      -> (* no such operator *)
           cont (pop1 s1) buff tk
       end
    | _ -> cont (pop1 s1) buff tk
  and begin_functor cont fail x buff tk =
    dbg "begin_functor %a@\n" pp_token tk;
    match tk with
    | `LPar -> token (term `OTHER (end_functor cont fail x []) fail) fail buff
    | _     -> cont (atom x) buff tk
  and end_functor (cont :  (term,'a) cont) fail name args a buff tk =
    dbg "end_functor %a@\n" pp_token tk;
    match tk with
    | `RPar   -> token (cont (pred name (List.rev @@ a::args))) fail buff
    | `Op "," -> token (term `OTHER (end_functor cont fail name (a::args)) fail) fail buff
    | `Atom _
    | `Op _   -> op `OTHER (end_functor cont fail name args) fail a buff tk
    | _       -> fail buff MalformedPredicate
  and close_parens cont fail s buff tk =
    dbg "expr_parens@\n";
    match tk with
    | `RPar -> token (cont s) fail buff
    | `Atom _
    | `Op _ -> op `NONE (close_parens cont fail) fail s buff tk
    | tk    -> fail buff UnbalancedParentheses
  and close_bracket cont fail s buff tk =
    dbg "expr_list@\n";
    match tk with
    | `RBra -> token (cont (list s)) fail buff
    | `Atom _
    | `Op _ -> op `CONS (close_bracket cont fail) fail s buff tk
    | tk    -> fail buff UnbalancedParentheses
  in
  let cont t buff = function
    | `Dot -> cont buff t
    | tk   -> fail buff (UnexpectedToken tk) in
  token (term `NONE (op `NONE cont fail) fail) fail buff

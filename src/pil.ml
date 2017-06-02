open Kernel

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
  | Eval.TypeError s            -> fprintf ppf "type error: %s" s
  | Eval.StaticProcedure k      -> fprintf ppf "cannot modify static value %a" Reg.PP.key k
  | Eval.DomainError k          -> fprintf ppf "domain error : %s" k
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

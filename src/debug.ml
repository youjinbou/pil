
let is_active = ref false

let activate () =
  is_active := true

let dbg_true = fun msg -> Format.eprintf msg
let dbg_false = fun msg -> Format.(ifprintf err_formatter) msg

let printf msg =
  if !is_active then dbg_true msg else dbg_false msg

let _ =
  CmdLine.add_params [
    "-d", Arg.Unit activate, "activate debugging display";
  ]

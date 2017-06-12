open Arg

let specs_ :(Arg.key * Arg.spec * Arg.doc) list ref = ref []

let add_params l =
  specs_ := l @ !specs_

let specs () = !specs_

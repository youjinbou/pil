open PList

module HT = Hashtbl

module S = struct type t = string let equal x y = x = y let hash = HT.hash end
module I = struct type t = int let equal x y = x == y let hash x = x end
module StringMap = HT.Make(S)
module IntMap = HT.Make(I)

type t = { mutable c : int; addresses : int StringMap.t; strings : string IntMap.t }
let store = { c = 0; addresses = StringMap.create 211; strings = IntMap.create 211 }

let atom x =
  try StringMap.find store.addresses x
  with Not_found -> let r = store.c in
                    store.c <- succ r;
                    StringMap.add store.addresses x r;
                    IntMap.add store.strings r x;
                    r
let string x =
  IntMap.find store.strings x

let sbuiltins = "," @& ";" @& ":-" @& "true" @& "false" @& "=" @& "is" @& "op" @& "|" @& "[|]" @& "[]" @& N
let builtins = PList.map atom sbuiltins
let (C (scomma, C (ssemicolon, C (sturnstile, C (strue, C (sfalse,
     C (sequal, C (sis, C (sop, C (spipe, C (scons, C (snil, N)))))))))))) = sbuiltins
let (C (comma, C (semicolon, C (turnstile, C (true_, C (false_,
     C (equal, C (is, C (op, C (pipe, C (cons, C (nil, N)))))))))))) = builtins

module OpKinds = struct
  let sops = PList.map snd OpKind.strings
  let ops = PList.map atom sops
  let (C (xfx, C (xfy, C (yfx, C (fx, C (fy, C (xf, C(yf,N)))))))) = ops
end

module Arith = struct

  let sops = "+" @& "*" @& "-" @& "/" @& N
  let ops =  PList.map atom sops

  let spreds = ">" @& "<" @& ">=" @& "=<" @& "=:=" @& N
  let preds = PList.map atom spreds

end

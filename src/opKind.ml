open PList

type t = Xfx | Xfy | Yfx | Fx | Fy | Xf | Yf

let strings = (Xfx,"xfx") @& (Xfy,"xfy") @& (Yfx,"yfx") @& (Fx,"fx") @& (Fy,"fy") @& (Xf,"xf") @& (Yf,"yf") @& N

let pp ppf k = Fmt.string ppf (PList.assoc k strings)

let arity = function
  | Xfx | Xfy | Yfx   -> 2
  | Fx | Fy | Xf | Yf -> 1

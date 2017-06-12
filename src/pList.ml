(* the following let us have simple type level lengths for lists, it 
 * permits several operations, as well as matching lists in let bindings
 * without warnings (actually, the reason it's being used). *)

type ('a, 'b) l =
    N : ('a, [ `Nil ]) l
  | C : 'a * ('a, 'b) l -> ('a, [ `Cons of 'b ]) l

let (@&) a b = C (a,b)

let rec map  : type t. ('a -> 'b) -> ('a, t) l -> ('b, t) l = fun f l ->
  match l with
  | N       -> N
  | C (a,b) -> C (f a, map f b)

let rec map2 : type t. ('a -> 'b -> 'c) -> ('a, t) l -> ('b, t) l -> ('c, t) l =
  fun f l1 l2 ->
  match l1, l2 with
  | N, N -> N
  | C(a1,b1), C(a2,b2) -> C(f a1 a2, map2 f b1 b2);;

let rec assoc : type t. 'a -> (('a*'b), t) l -> 'b = fun k l ->
  match l with
  | N -> raise Not_found
  | C ((a,b),c) when a = k -> b
  | C (a,b) -> assoc k b

let rec iter : type t. ('a -> unit) -> ('a, t) l -> unit = fun f -> function
  | N -> ()
  | C (a,b) -> f a; iter f b

let rec fold : type t. ('a -> 'b -> 'b) -> ('a, t) l -> 'b -> 'b  = fun f l acc ->
  match l with
  | N -> acc
  | C (a,b) -> fold f b (f a acc)

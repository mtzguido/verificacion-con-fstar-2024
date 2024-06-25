module Clase13.DEQ

open FStar.Tactics.Typeclasses

// noeq
// type deq (a:Type) = {
//   ( =? ) : a -> a -> Tot bool;
// }
class deq (a:Type) = {
  ( =? ) : a -> a -> Tot bool;
}

// [@@tcinstance]
// let eq_int : deq int = {
//   ( =? ) = (fun x y -> x=y);
// }
instance eq_int : deq int = {
  ( =? ) = (fun x y -> x=y);
}

let xx = assert ((1 =? 2) == false)

type abc = | A | B | C

instance eq_abc : deq abc = {
  ( =? ) = (fun x y ->
              match x, y with
              | A, A
              | B, B
              | C, C -> true
              | _ -> false);
}
// instance eq_abc' : deq abc = {
//   ( =? ) = (fun x y -> false);
// }

let rec eq_list_f (#t:Type) {| deq_t : deq t |} (xs ys : list t) : Tot bool =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> x =? y && eq_list_f xs ys
  | _ -> false

instance eq_list #t (_ : deq t) : deq (list t) = {
  ( =? ) = eq_list_f;
}

// instance Eq a => Eq [a] where
//   []     == []       = True
//   (x:xs) == (y:ys)   = x == y && xs == ys
//   _      == _        = False

let _ = assert (eq_list_f #_ #eq_abc [A] [] == false)
let _ = assert ([A] =? [] == false)

let test (t:Type) {| d : deq t |} (x:t) =
  assert ([x] =? [] == false)

let cmp_true (t:Type) : deq t = {
  ( =? ) = (fun _ _ -> true);
}

// Nada previene romper canonicidad
let _ = assert ( (=?) #int #(cmp_true int) 1 2   == true )

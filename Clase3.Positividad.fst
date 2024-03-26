module Clase3.Positividad

(* Positividad *)

// noeq
// type ni =
//   | Mk : f:(ni -> empty) -> ni

assume val ni : Type
assume val mk : (ni -> empty) -> ni
assume val mkf : ni -> (ni -> empty)

let self_app (x : ni) : empty =
  (mkf x) x
  
let boxed : ni =
  mk self_app

let raro () : empty =
  self_app boxed

(*
     self_app boxed
  ~> self_app (mk self_app)
  ~> f (mk self_app) (mk self_app)
  ~> self_app (mk self_app)
  ~> ...
*)

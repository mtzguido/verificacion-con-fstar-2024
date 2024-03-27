module Clase2.DeMorgan

open Clase2

(* Este archivo muestra la equivalencia entre una de las leyes de De Morgan
(la que no vale en lógica intuicionista) con el axioma *débil* del tercero
excluído.

Ver también: https://en.wikipedia.org/wiki/De_Morgan%27s_laws#In_intuitionistic_logic
*)

(* Ley débil del tercero excluído *)
type lted = (a:Type0) -> oo (no a) (no (no a))
(* Ley de De Morgan, no válida en lógica intuicionista *)
type dm1v = (#a:Type0 -> #b:Type0 -> no (yy a b) -> oo (no a) (no b))

val dm1v_implica_lte_debil : dm1v -> lted
let dm1v_implica_lte_debil
  (ax : dm1v)
  : lted
= fun a -> ax #a #(no a) no_contradiccion

val lte_debil_implica_dm1v : lted -> dm1v
let lte_debil_implica_dm1v
  (ax : lted) : dm1v
=
  fun (#a #b : Type) (pf : no (yy a b)) ->
    match ax b with
    | Inl nb -> Inr nb
    | Inr nnb ->
      (* Tenemos:
           (b -> falso) -> falso
           (a /\ b) -> falso
         Demostramos a -> falso.
         La intuición es que si tenemos la prueba de a, podemos convertir
         la función
           (a /\ b) -> falso
         a
           b -> falso
         "aplicando" la prueba en la primer componente del par
      *)
      let na : no a =
        fun x ->
          let nb = (fun (y:b) -> pf (x, y)) in
          nnb nb
      in
      Inl na

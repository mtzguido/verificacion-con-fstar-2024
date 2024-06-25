module Clase13.Listas

open Container

instance val listas_son_container0 (a:eqtype)
  : container0 a (list a)

instance val listas_son_container_laws (a:eqtype)
  : container_laws a (list a) (listas_son_container0 a)

instance val listas_son_container (a:eqtype)
  : container a (list a)

// val trie (a:Type) : Type
// instance val trie_son_container0 (a:eqtype)
//   : container0 (list a) (trie a)

// val rbt (a:Type) : Type
// instance val rbt_son_container0 (a:eqtype)
//   : container0 a (rbt a)

(* Los siguientes tests fallan sin conocer las implementaciones
(funciona dentro del módulo, porque mem/ins/del son visibles.
Se puede _demostrar_ (si tenemos la instancia de _laws)
pero no es automático. *)

// let test0 () =
//   let l : list int = empty in
//   let l = ins 2 l in
//   let l = del 3 l in
//   assert (mem 2 l);
//   l

// let test1 (t:eqtype) (x:t) =
//   let l : list t = empty in
//   let l = ins x l in
//   assert (mem x l);
//   l

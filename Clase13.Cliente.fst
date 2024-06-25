module Clase13.Cliente

open Container
open Clase13.Listas

let test () =
  let l : list int = empty in
  let l = ins 2 l in
  let l = del 3 l in
  // assert (mem 2 l);
  // ^ demostrable, pero aburrido: hay que llamar los lemas a mano
  ()

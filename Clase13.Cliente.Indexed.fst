module Clase13.Cliente.Indexed

open Container.Indexed
open Clase13.Listas

let test #s {| icontainer int s |} () =
  let e : s _ = empty in
  let e = ins 1 e in
  let e = ins 2 e in
  let e = ins 3 e in
  let e = ins 4 e in
  let e = del 2 e in
  assert (mem 1 e);
  assert (not (mem 2 e));
  assert (mem 3 e);
  assert (mem 4 e);
  ()

let test_list () =
  test #_ #(icontainer_from_container int (list int)
               FStar.Tactics.Typeclasses.solve) ()

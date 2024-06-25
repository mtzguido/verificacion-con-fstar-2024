module Clase13.Listas

open Container

// [@@"opaque_to_smt"]
let rec mem (#a:eqtype) (y:a) (xs : list a) : bool =
  match xs with
  | [] -> false
  | x::xs -> x=y || mem y xs

let ins = Cons

let rec del (#a:eqtype) (y:a) (xs : list a) : list a =
  match xs with
  | [] -> []
  | x::xs ->
    if x = y
    then del y xs
    else x :: del y xs

instance listas_son_container0 (a:eqtype)
  : container0 a (list a) = {
    empty = [];
    is_empty = Nil?;

    mem = mem;
    ins = ins;
    del = del;
  }


let models (#a:eqtype)
  (xs : list a)
  (ss : TSet.set a)
  : GTot prop =
  forall (x:a).
    mem x xs <==> TSet.mem x ss

// Discriminador:
// let Nil? = function | Nil -> true | _ -> false

(* Raro! *)
let is_empty_ok_back (#a:eqtype) (xs:list a)
  : Lemma (models xs TSet.empty ==> Nil? xs)
  = match xs with
    | _::_ -> ()
    | [] -> ()

let ins_ok_lem (#a:eqtype) (x:a) (xs:list a) (ss : TSet.set a)
  : Lemma (requires xs `models` ss)
          (ensures  ins x xs
                     `models`
                    TSet.union ss (TSet.singleton x))
  =
  ()

let rec del_ok_aux (#a:eqtype) (y:a) (xs:list a) (z:a)
  : Lemma (mem z (del y xs) <==> mem z xs /\ y <> z)
  = match xs with
    | [] -> ()
    | x::xs -> del_ok_aux y xs z

let del_ok_lem (#a:eqtype) (y:a) (xs:list a) (ss : TSet.set a)
  : Lemma (requires xs `models` ss)
          (ensures del y xs
                   `models`
                   TSet.intersect ss (TSet.complement <| TSet.singleton y))
  =
  Classical.forall_intro (del_ok_aux y xs)


instance listas_son_container_laws (a:eqtype)
  : container_laws a (list a) (listas_son_container0 a) = {
    models = models;
    empty_ok = (fun () -> ());
    is_empty_ok = (fun st -> is_empty_ok_back st);
    mem_ok = (fun _ _ _ -> ());
    ins_ok = ins_ok_lem;
    del_ok = del_ok_lem;
}

instance listas_son_container (a:eqtype)
  : container a (list a) = {
    ops = listas_son_container0 a;
    laws = listas_son_container_laws a;
  }

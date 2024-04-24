module Clase6.BST

open FStar.Mul
open FStar.List.Tot
open FStar.Ghost

let max (x y : int) : int = if x > y then x else y

type bst0 =
  | L
  | N of bst0 & int & bst0

let rec all_lt (x: int) (t: bst0) : bool =
  match t with
  | L -> true
  | N (l, y, r) -> all_lt x l && y < x && all_lt x r

let rec all_gt (x: int) (t: bst0) : bool =
  match t with
  | L -> true
  | N (l, y, r) -> all_gt x l && y > x && all_gt x r

let rec is_bst (t: bst0) : bool =
  match t with
  | L -> true
  | N (l, x, r) -> is_bst l && is_bst r && all_lt x l && all_gt x r

type bst = b:bst0{is_bst b}

let rec insert0 (x: int) (t: bst0) : bst0 =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: NO admite duplicados *)
    if x = y then t
    else if x < y then N (insert0 x l, y, r)
    else N (l, y, insert0 x r)

let insert0_all_lt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_lt y t /\ x < y)
          (ensures all_lt y (insert0 x t))
  =
  admit()

let insert0_all_gt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_gt y t /\ x > y)
          (ensures all_gt y (insert0 x t))
  =
  admit()
    
let insert0_bst (x:int) (t:bst0) : Lemma (requires is_bst t) (ensures is_bst (insert0 x t)) =
  admit()

let insert (x:int) (t:bst) : bst =
  insert0_bst x t;
  insert0 x t

(* Nota: al usar GTot nos aseguramos que esta función sólo se usa
en contextos de especificación, y nunca en código ejecutable. ¿Hay otras
funciones que pueden marcarse así? *)
let rec in_tree (x:int) (t:bst0) : GTot bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    x = y || in_tree x l || in_tree x r

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let member_ok (x:int) (t:bst) : Lemma (member x t == in_tree x t) =
  admit()

let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) <= 1 + size t) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    insert_size x l;
    insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height t <= height (insert x t) /\ height (insert x t) <= 1 + height t)
= match t with
  | L -> ()
  | N (l, y, r) ->
    insert_height x l;
    insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    if x <= y
    then insert_mem x l
    else insert_mem x r
  
let all_lt_trans (x y : int) (t : bst0) : Lemma (requires all_lt x t /\ y >= x) (ensures all_lt y t) =
  admit()

let all_gt_trans (x y : int) (t : bst0) : Lemma (requires all_gt x t /\ y <= x) (ensures all_gt y t) =
  admit()

// NB: cambiado para fortalecer la precondición, y no devolver una opción.
let rec extract_min0 (t: bst0{N? t}) : int & bst0 =
  match t with
  | N (L, x, r) -> (x, r)
  | N (l, x, r) ->
    let (min, l') = extract_min0 l in
    let t : bst0 = N (l', x, r) in
    (min, t)

let extract_min_preserva_all_lt (y:int) (t : bst0{N? t})
  : Lemma (requires is_bst t /\ all_lt y t)
          (ensures all_lt y (snd (extract_min0 t)))
= admit()

let extract_min_es_bst (t:bst0{N? t})
: Lemma (requires is_bst t)
        (ensures is_bst (snd (extract_min0 t)))
=
  admit()

let extract_min (t: bst{N? t}) : (int & bst) =
  admit()

let delete_root0 (t: bst0{N? t}) : bst0 =
  let N (l, _, r) = t in
  if r = L then l
  else
    let (x, r') = extract_min0 r in
    N (l, x, r')

let rec delete0 (x: int) (t: bst0) : bst0 =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete0 x l, y, r)
    else if x > y then N (l, y, delete0 x r)
    else delete_root0 t
    
(* Se puede demostrar que delete preserva BSTs... pero es engorroso. Sólo
intentar si completaron todo y tienen ganas de renegar un rato. *)

module Clase3.Recursion
  
(* Recursion y medidas *)

let rec add (m n : nat) : Tot nat (decreases n) =
  if n = 0 then m
  else add (m+1) (n-1)
  
(* Demuestre la terminación de esta función *)
let rec countdown (x:int) : Tot nat =
  admit(); // borrar
  if x <= -5 then 0
  else (
    countdown (x-1)
  )

// Elija una métrica para demostrar la terminación
let rec count_up (x:int{x <= 0}) : Tot unit =
  admit();
  if x = 0 then ()
  else count_up (x+1)

let b2nat : bool -> nat = function | false -> 0 | true -> 1

(* Una función con métrica lexicográfica. `x` puede aumentar si
`b` disminuye. Nota: no tenemos que `false << true` (tal vez debería
ser cierto.. pero actualmente no lo es) así que convertimos el booleano
a un natural para la métrica. *)
let rec f (b:bool) (x:nat) : Tot nat (decreases %[b2nat b; x]) =
  if x = 0 then 0
  else if b
  then 1 + f false (x+100)
  else 1 + f b (x-1)

(* A veces, al escribir funciones mutuamente recursivas, ningún argumento
decrece en una llamada en particular, pero eso sólo ocurre *en una dirección*,
en este caso en las llamadas de gg a ff. Para modelar eso, podemos agregar
una constante a la claúsula decreases en cada función.

 La llamada a gg (x-1) dentro de ff es correcta porque  (x-1, 1) << (x, 0)

 La llamada a ff x dentro de gg es correcta porque  (x, 0) << (x, 1)

*)
let rec ff (x:nat) : Tot nat (decreases %[x; 0]) =
  if x = 0 then 0
  else gg (x-1)
and gg (x:nat) : Tot nat (decreases %[x; 1]) =
  1 + ff x
 
// -5 -> 4 -> -3 -> 2 -> -1 -> 0
// Elija una métrica para demostrar la terminación
let rec flip (x:int) : Tot int =
  admit(); // borrar
  if x = 0 then 0
  else if x > 0 then flip (-x + 1)
  else (* x < 0 *) flip (-x - 1)

// -5 -> 4 -> -4 -> 3 -> -3 -> 2 -> -2 -> 1 -> -1 -> 0
// Elija una métrica para demostrar la terminación (un poco más dificil)
let rec flip2 (x:int) : Tot int =
  admit(); // borrar
  if x = 0 then 0
  else if x > 0 then flip2 (-x)
  else (* x < 0 *) flip2 (-x - 1)

let rev (#a:Type) (xs : list a) : list a =
  admit(); // borrar
  (* Agregar una claúsula para demostrar la terminación de esta función *)
  let rec go (acc xs : list a) : Tot (list a) =
    match xs with
    | [] -> acc
    | x::xs -> go (x::acc) xs
  in
  go [] xs

let rec sum (xs:list int) : int =
  (* Por qué se acepta esta función? *)
  if Nil? xs
  then 0
  else List.Tot.hd xs + sum (List.Tot.tl xs)

(* Prefijo de una lista *)
let rec init #a (xs : list a{Cons? xs}) : list a =
  match xs with
  | [x] -> []
  | x::xs -> x :: init xs

(* Último elemento *)
let rec last #a (xs : list a{Cons? xs}) : a =
  match xs with
  | [x] -> x
  | _::xs -> last xs

[@@expect_failure]
let rec sum' (xs:list int) : Tot int =
  (* Por qué *no* se acepta esta función? Termina? *)
  if Nil? xs
  then 0
  else last xs + sum' (init xs)

(* La función de Ackermann se chequea correctamente 
con la métrica por defecto. *)
let rec ack (m n : nat) : nat =
  if m = 0 then n+1
  else if n = 0 then ack (m-1) 1
  else ack (m-1) (ack m (n-1))

(* Demostar que esta version con los argumentos al revés termina. *)
let rec ack' (n m : nat) : Tot nat =
  admit(); // borrar
  if m = 0 then n+1
  else if n = 0 then ack' 1 (m-1)
  else ack' (ack' (n-1) m) (m-1)

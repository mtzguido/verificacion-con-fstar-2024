module Clase1

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul

let suma (x y : int) : int = x + y

(* Defina una función suma sobre naturales *)
let addnat (x y : nat) : nat = admit()

(* Defina una función suma de 3 argumentos, que use la anterior. *)
let suma3 (x y z : int) : int = admit()

(* Defina una función que incremente un número en 1. *)
let incr (x:int) : int = admit()

(* Dé más tipos a la función de incremento. ¿Cómo se comparan
estos tipos? *)
let incr'   (x:nat) : int = admit()
let incr''  (x:nat) : nat = admit()
let incr''' (x:nat) : y:int{y = x+1} = admit()

(* Un tipo refinado es un subtipo del tipo base, se puede
usar sin coerción. El subtipado es también consciente de funciones. *)
let addnat' (x y : nat) : int = x + y

let debilitar1 (f : int -> int) : nat -> int = f
let debilitar2 (f : nat -> nat) : nat -> int = f
let debilitar3 (f : int -> nat) : nat -> int = f

let par   (x:int) : bool = x % 2 = 0
let impar (x:int) : bool = x % 2 = 1

(* Dadas estas definiciones, dé un tipo a incr que diga
que dado un número par, devuelve un número impar. *)	
let incr'''' (x:int{par x}) : y:int{impar y} = x + 1

(* ¿Por qué falla la siguiente definición? Arreglarla. *)
// El atributo expect_failure causa que F* chequeé que la definición
// subsiguiente falle. Borrarlo para ver el error real.
[@@expect_failure]
let muldiv (a b : int) : y:int{y = a} = (a / b) * b

(* Defina una función de valor absoluto *)
let abs (x:int) : nat = admit()

(* Defina una función que calcule el máximo de dos enteros. *)
let max (x y : int) : int = admit()

(* Dé tipos más expresivos a max.
   1- Garantizando que el resultado es igual a alguno de los argumentos
   2- Además, garantizando que el resultado es mayor o igual a ambos argumentos. *)

(* Defina la función de fibonacci, de enteros a enteros,
o alguna restricción apropiada. *)
let fib (x:int) : int = admit()

(* Defina un tipo 'digito' de naturales de un sólo dígito. *)
// type digito =

(* Defina una función que compute el máximo de tres dígitos, usando
alguna definición anterior. El resultado debe ser de tipo digito.
¿Por qué funciona esto? ¿De cuáles partes anteriores del archivo
depende, exactamente? *)
// let max_digito (x y z : digito) : digito =

(* Defina la función factorial. ¿Puede darle un mejor tipo? *)
let fac (x:int) : int = admit()

(* Defina una función que sume los números naturales de 0 a `n`. *)
let triang (n:nat) : nat = admit()

(* Intente darle un tipo a fib que diga que el resultado es siempre
mayor o igual al argumento. Si el chequeo falla, dé hipótesis de por qué. *)
//let fib' : ... = ...

(* Idem para la función factorial. *)
//let fac' : ... = ...

(* Defina la siguiente función que suma una lista de enteros. *)
val sum_int : list int -> int
let sum_int xs = admit()

(* Defina la siguiente función que revierte una lista de enteros. *)
val rev_int : list int -> list int
let rev_int xs = admit()

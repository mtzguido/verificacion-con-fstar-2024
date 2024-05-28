module Clase10.Calc

(* Algoritmo extendido de Euclides *)

open FStar.Mul

(* [a] divide a [b] *)
let ( /? ) a b = exists (c:int). a * c == b

let intro_divides (a b : int) (c : int)
  : Lemma (a * c == b ==> a /? b)
  = ()

let is_cd (x y : nat) (z : nat) = z /? x /\ z /? y

let is_gcd (x y : nat) (z : nat) =
  is_cd x y z /\ (forall z'. z' > z ==> ~ (is_cd x y z'))

let div_neg (x y : int)
: Lemma (requires x /? y)
        (ensures  x /? (-y))
        [SMTPat (x /? (-y))]
=
  let aux (c:int) : Lemma (x*c == y ==> x /? (-y)) =
    intro_divides x (-y) (-c);
    ()
  in
  let aux2 () : Lemma (forall c. x*c == y ==> x /? (-y)) =
    Classical.forall_intro aux
  in
  aux2 ()
  // assert (forall c. c*x == y ==> x*(-c) == (-y))

let mayor_no_div (x:pos) (z':int)
: Lemma (requires z' > x /\ z' /? x)
        (ensures False)
=
  ()

let lem_gcd_0 (x:pos) : Lemma (is_gcd x 0 x) =
  assert (1 * x == x);
  assert (x /? x);
  assert (x /? 0);
  assert (is_cd x 0 x);
  ()

let lem_gcd_sym (x y g : nat)
: Lemma (requires is_gcd x y g)
        (ensures is_gcd y x g)
=
  ()

let div_add (x y z : int)
: Lemma (requires z /? x /\ z /? y)
        (ensures z /? (x+y))
=
  let aux (c1 c2 : int) : Lemma (requires c1*z == x /\ c2*z==y)
                                (ensures z /? (x+y))
  =
    calc (==) {
      (c1+c2)*z;
      == {}
      c1*z + c2*z;
      == {}
      x + y;
    };
    // assert ((c1+c2)*z == x+y);
    intro_divides z (x+y) (c1+c2);
    ()
  in
  assert (exists c1. c1 * z == x);
  assert (exists c2. c2 * z == y);
  assert (exists c1 c2. c1 * z == x /\ c2 * z == y);
  Classical.forall_intro_2 (fun c1 -> Classical.move_requires (aux c1));
  ()

let div_sub (x y z : int)
: Lemma (requires z /? x /\ z /? y)
        (ensures z /? (x-y))
=
  div_add x (-y) z;
  assert (z /? (x + (-y)));
  assert (z /? (x - y));
  ()

let lem_gcd_add (x y g : nat)
: Lemma (requires is_gcd x y g)
        (ensures is_gcd x (x+y) g)
=
  let aux (z:nat) : Lemma (is_cd x y z <==> is_cd x (x+y) z) =
    calc (<==>) {
        is_cd x y z;
        <==> {}
        z /? x /\ z /? y;
        <==> { Classical.move_requires (div_add x y) z;
               Classical.move_requires (div_sub (x+y) x) z }
        z /? x /\ z /? (x+y);
        <==> {}
        is_cd x (x+y) z;
    }
  in
  Classical.forall_intro aux;
  ()

let lem_gcd_sub (x y g : nat)
: Lemma (requires x >= y)
        (ensures is_gcd x y g <==> is_gcd (x-y) y g)
=
  let aux (z:nat) : Lemma (is_cd x y z <==> is_cd (x-y) y z) =
    calc (<==>) {
        is_cd x y z;
        <==> {}
        z /? x /\ z /? y;
        <==> { Classical.move_requires (div_sub x y) z;
               Classical.move_requires (div_add (x-y) y) z }
        z /? (x-y) /\ z /? y;
        <==> {}
        is_cd (x-y) y z;
    }
  in
  Classical.forall_intro aux;
  ()

let rec lem_gcd_mod (x y g : nat)
: Lemma (requires y <> 0)
        (ensures is_gcd x y g <==> is_gcd (x%y) y g)
=
  if x < y then (
    calc (<==>) {
      is_gcd x y g;
      <==> { Math.Lemmas.small_mod x y; assert (x%y == x) }
      is_gcd (x%y) y g;
    }
  ) else (
    calc (<==>) {
      is_gcd x y g;
      <==> { lem_gcd_sub x y g }
      is_gcd (x-y) y g;
      <==> {
        Math.Lemmas.sub_div_mod_1 x y;
        assert ((x-y)%y == x%y);
        lem_gcd_mod (x-y) y g
      }
      is_gcd (x%y) y g;
    }
  )

let gcd_of (x y : nat) : Type =
  (a:int & b:int & g:nat{a*x + b*y == g /\ is_gcd x y g})

let rec egcd (x y : nat)
: Pure (gcd_of x y)
       (requires x <> 0 \/ y <> 0)
       (ensures fun _ -> True)
       (decreases y)
=
  if x = 0 then (
    lem_gcd_0 y;
    (| 0, 1, y |)
  ) else if y = 0 then (
    lem_gcd_0 x;
    (| 1, 0, x |)
  ) else if x < y then (
    let (| a, b, g |) = egcd y x in
    (| b, a, g |)
  ) else (
    let (| a, b, g |) = egcd y (x%y) in
    assert (a*y + b*(x%y) == g);
    let r = x/y in
    assert (is_gcd y (x%y) g);
    assert (y <> 0);
    lem_gcd_mod x y g;
    assert (is_gcd x y g);
    (*
    calc (==) {
      b*x + (a-b*r)*y;
      == {}
      b*x + (a-b*(x/y))*y;
      == { Math.Lemmas.distributivity_sub_left a (b*(x/y)) y }
      b*x + a*y - b*(x/y)*y;
      == { Math.Lemmas.paren_mul_right b (x/y) y }
      b*x + a*y - b*((x/y)*y);
      == { Math.Lemmas.distributivity_sub_right b x ((x/y)*y) }
      a*y + b * (x - (x/y)*y);
      == { Math.Lemmas.euclidean_division_definition x y }
      a*y + b * (x%y);
      == { () }
      g;
    };
    *)
    (* o más simplemente (y rápido!), con canon: *)
    calc (==) {
      b*x + (a-b*r)*y;
      == {}
      b*x + (a-b*(x/y))*y;
      == { _ by (Tactics.Canon.canon ()) }
      a*y + b * (x - (x/y)*y);
      == { Math.Lemmas.euclidean_division_definition x y }
      a*y + b * (x%y);
      == { () }
      g;
    };
    (| b, a-b*(x/y), g |)
  )

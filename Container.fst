module Container

open FStar.Tactics.Typeclasses

// Haskell: | s -> e
[@@fundeps [0]] // "el arg 0 es definido por el resto... es decir s -> e"
class container0 (e s : Type) : Type = {
  empty    : s;
  is_empty : s -> bool;

  mem    : e -> s -> bool;
  ins    : e -> s -> s;
  del    : e -> s -> s;
}

[@@fundeps [0]]
class container_laws (e s : Type) (_ : container0 e s) : Type = {
  models : s -> TSet.set e -> prop;
  empty_ok :
    unit -> Lemma (models empty TSet.empty);

  is_empty_ok :
    (st:s) ->
      Lemma (is_empty st <==> models st TSet.empty);

  mem_ok :
    (x:e) -> (st:s) -> (ss : TSet.set e) ->
      Lemma (requires models st ss)
            (ensures  mem x st <==> TSet.mem x ss);

  ins_ok :
    (x:e) -> (st:s) -> (ss : TSet.set e) ->
      Lemma (requires st `models` ss)
            (ensures  ins x st
                      `models`
                      // ss U {x}
                      TSet.union ss (TSet.singleton x));

  del_ok :
    (x:e) -> (s:s) -> (ss : TSet.set e) ->
      Lemma (requires s `models` ss)
            (ensures  del x s
                      `models`
                      // ss \ {x}
                      TSet.intersect ss (TSet.complement <| TSet.singleton x));
}

[@@fundeps [0]]
class container (e s : Type) : Type = {
  ops  : container0 e s;
  laws : container_laws e s ops;
}

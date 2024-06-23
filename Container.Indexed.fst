module Container.Indexed

open Container
open FStar.Tactics.Typeclasses

[@@fundeps [0]]
class icontainer (e : Type) (s : TSet.set e -> Type) : Type = {
  empty  : s TSet.empty;

  is_empty : #es:_ -> s es -> bool;
  mem    : #es:TSet.set e -> x:e -> s es ->
             b:bool{b <==> TSet.mem x es};
  ins    : #es:TSet.set e -> x:e -> s es ->
             s (TSet.union es (TSet.singleton x));
  del    : #es:TSet.set e -> x:e -> s es ->
             s (TSet.intersect es (TSet.complement <| TSet.singleton x));
}

let refined (#e:Type) (s:Type) {| d : container e s |} (es : TSet.set e) : Type =
  st:s & squash (d.laws.models st es)

let icontainer_from_container (e s : Type) (d : container e s) : icontainer e (refined #e s) = {
  empty = (| d.ops.empty, d.laws.empty_ok () |);
  is_empty = (fun st -> d.ops.is_empty (dfst st));
  mem = (fun (#es:TSet.set e) (x:e) (st : refined #e s es) ->
           d.laws.mem_ok x (dfst st) es; d.ops.mem x (dfst st));
  ins = (fun (#es:TSet.set e) (x:e) (st : refined #e s es) ->
           (| d.ops.ins x (dfst st), d.laws.ins_ok x (dfst st) es |));
  del = (fun (#es:TSet.set e) (x:e) (st : refined #e s es) ->
           (| d.ops.del x (dfst st), d.laws.del_ok x (dfst st) es |));
}

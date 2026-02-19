open Dynarray

type 'a array = 'a t

let def__Array_get_u33Internal _ _ arr idx =
  let i = Z.to_int idx in
  if 0 <= i && i < length arr then get arr i else assert false

let def__Array_swap _ arr idx jdx _ _ =
  let i = Z.to_int idx in
  let j = Z.to_int jdx in
  if 0 <= i && i < length arr && 0 <= j && j < length arr then
    let vi = get arr i in
    let vj = get arr j in
    set arr j vi;
    set arr i vj;
    arr
  else assert false

let def__Array_getInternal _ arr idx _ =
  let i = Z.to_int idx in
  get arr i

let def__Array_size _ arr = Z.of_int (length arr)

let def__Array_emptyWithCapacity _ cap =
  let arr = create () in
  ensure_capacity arr (Z.to_int cap);
  arr

let def__Array_push _ arr v = add_last arr v; arr

let def__Array_set_u33 _ arr idx v =
  let i = Z.to_int idx in
  set arr i v;
  arr

let def__Array_mk _ l = of_list l

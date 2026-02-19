open Sek.Persistent

type 'a array = 'a Sek.P.t

let def__Array_get_u33Internal _ _ arr idx =
  let i = Z.to_int idx in
  if 0 <= i && i < length arr then get arr i else assert false

let def__Array_swap _ arr idx jdx _ _ =
  let i = Z.to_int idx in
  let j = Z.to_int jdx in
  if 0 <= i && i < length arr && 0 <= j && j < length arr then
    let vi = get arr i in
    let vj = get arr j in
    let arr = set arr j vi in
    let arr = set arr i vj in
    arr
  else assert false

let def__Array_getInternal _ arr idx _ =
  let i = Z.to_int idx in
  get arr i

let def__Array_size _ arr = Z.of_int (length arr)

let def__Array_emptyWithCapacity _ cap = create (Obj.magic 0)

let def__Array_push _ arr v = push Sek.back arr v

let def__Array_set_u33 _ arr idx v =
  let i = Z.to_int idx in
  set arr i v

let def__Array_mk _ l = of_list (Obj.magic 0) l

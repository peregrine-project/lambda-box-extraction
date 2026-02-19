(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Persistent arrays implemented using Baker's trick.

   A persistent array is a usual array (node Array) or a change into
   another persistent array (node Diff). Invariant: any persistent array is a
   (possibly empty) linked list of Diff nodes ending on an Array node.

   As soon as we try to access a Diff, we reverse the linked list to move
   the Array node to the position we are accessing; this is achieved with
   the reroot function.
*)

type 'a t = 'a data ref

and 'a data =
  | Array of 'a Dynarray.t
  | Diff of int * 'a * 'a t
  | Push of 'a * 'a t
  | Pop of 'a t

let make n v =
  ref (Array (Dynarray.make n v))

let create ?capacity () =
  let d = Dynarray.create () in
  Option.iter (Dynarray.ensure_capacity d) capacity;
  ref (Array d)
  

let init n f =
  ref (Array (Dynarray.init n f))

(* `reroot t` ensures that `t` becomes an `Array` node.
    This is written in CPS to avoid any stack overflow. *)
let rec rerootk t k = match !t with
  | Array _ -> k ()
  | Diff (i, v, t') ->
      rerootk t' (fun () ->
          (match !t' with
	   | Array a as n ->
	       let v' = Dynarray.get a i in
	       Dynarray.set a i v;
	       t := n;
	       t' := Diff (i, v', t)
	   | _ -> assert false
          );
          k()
        )
  | Push (v, t') ->
      rerootk t' (fun () ->
          (match !t' with
	   | Array a as n ->
	       Dynarray.add_last a v;
	       t := n;
	       t' := Pop t
	   | _ -> assert false
          );
          k()
        )
  | Pop t' ->
      rerootk t' (fun () ->
          (match !t' with
	   | Array a as n ->
               let v' = Dynarray.pop_last a in
	       t := n;
	       t' := Push (v', t)
	   | _ -> assert false
          );
          k()
        )

let reroot t = rerootk t (fun () -> ())

let get t i =
  match !t with
  | Array a ->
      Dynarray.get a i
  | _ ->
      reroot t;
      (match !t with Array a -> Dynarray.get a i | _ -> assert false)

let set t i v =
  reroot t;
  match !t with
  | Array a as n ->
      let old = Dynarray.get a i in
      if old == v then
	t
      else (
	Dynarray.set a i v;
	let res = ref n in
	t := Diff (i, old, res);
	res
      )
  | _ ->
      assert false

let push t v =
  reroot t;
  match !t with
  | Array a as n ->
	Dynarray.add_last a v;
	let res = ref n in
	t := Pop res;
	res
  | _ ->
      assert false

(* CAVEAT: Do not use `with_array` with a function `f` that may reroot
   the persitent array `t` (for instance by accessing, even with `get`
   only, to other versions of `t`). *)
let with_array t f =
  reroot t;
  match !t with Array a -> f a | _ -> assert false

let length t =
  with_array t Dynarray.length

let to_list t =
  with_array t Dynarray.to_list

let iter f a =
  for i = 0 to length a - 1 do f (get a i) done

let iteri f a =
  for i = 0 to length a - 1 do f i (get a i) done

let fold_left f x a =
  let r = ref x in
  for i = 0 to length a - 1 do
    r := f !r (get a i)
  done;
  !r

let fold_right f a x =
  let r = ref x in
  for i = length a - 1 downto 0 do
    r := f (get a i) !r
  done;
  !r

(* Tests *)
let () =
  let a = create () in
  let b = push a 42 in
  assert (to_list b = [42]);
  assert (to_list a = []);
  assert (to_list b = [42]);
  ()

(* Shims to Lean names, see SekArray.ml *)
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
    let arr = set arr j vi in
    let arr = set arr i vj in
    arr
  else assert false

let def__Array_getInternal _ arr idx _ =
  let i = Z.to_int idx in
  get arr i

let def__Array_size _ arr = Z.of_int (length arr)

let def__Array_emptyWithCapacity _ cap =
  let capacity = Z.to_int cap in
  create ~capacity ()

let def__Array_push _ arr v = push arr v

let def__Array_set_u33 _ arr idx v =
  let i = Z.to_int idx in
  set arr i v

let def__Array_mk _ l =
  ref (Array (Dynarray.of_list l))

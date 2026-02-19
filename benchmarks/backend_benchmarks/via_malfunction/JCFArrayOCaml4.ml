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

(* Including the necessary parts of the OCaml 5 Dynarray implementation in here. *)
module type DYNARRAY = sig
  type !'a t
  val create : unit -> 'a t
  val make : int -> 'a -> 'a t
  val init : int -> (int -> 'a) -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> unit
  val length : 'a t -> int
  val add_last : 'a t -> 'a -> unit
  val pop_last : 'a t -> 'a
  val of_list :  'a list -> 'a t
  val to_list : 'a t -> 'a list
  val ensure_capacity : 'a t -> int -> unit
end

module Dynarray : DYNARRAY = struct
  module Dummy : sig
  
    (** {4 Dummies} *)
  
    type 'stamp dummy
    (** The type of dummies is parametrized by a ['stamp] variable,
        so that two dummies with different stamps cannot be confused
        together. *)
  
    type fresh_dummy = Fresh : 'stamp dummy -> fresh_dummy
    val fresh : unit -> fresh_dummy
    (** The type of [fresh] enforces a fresh/unknown/opaque stamp for
        the returned dummy, distinct from all previous stamps. *)
  
  
    (** {4 Values or dummies} *)
  
    type ('a, 'stamp) with_dummy
    (** a value of type [('a, 'stamp) with_dummy] is either a proper
        value of type ['a] or a dummy with stamp ['stamp]. *)
  
    val of_val : 'a -> ('a, 'stamp) with_dummy
    val of_dummy : 'stamp dummy -> ('a, 'stamp) with_dummy
  
    val is_dummy : ('a, 'stamp) with_dummy -> 'stamp dummy -> bool
    val unsafe_get : ('a, 'stamp) with_dummy -> 'a
    (** [unsafe_get v] can only be called safely if [is_dummy v dummy]
        is [false].
  
        We could instead provide
        [val find : ('a, 'stamp) with_dummy -> ('a, 'stamp dummy) result]
        but this would involve intermediary allocations.
  
        {[match find x with
          | None -> ...
          | Some v -> ...]}
        can instead be written
        {[if Dummy.is_dummy x
          then ...
           else let v = Dummy.unsafe_get x in ...]}
    *)
  
    (** {4 Arrays of values or dummies} *)
    module Array : sig
      val make :
        int -> 'a -> dummy:'stamp dummy ->
        ('a, 'stamp) with_dummy array
  
      val init :
        int -> (int -> 'a) -> dummy:'stamp dummy ->
        ('a, 'stamp) with_dummy array
  
      val copy : 'a array -> dummy:'stamp dummy -> ('a, 'stamp) with_dummy array
  
      val unsafe_nocopy :
        'a array -> dummy:'stamp dummy ->
        ('a, 'stamp) with_dummy array
      (** [unsafe_nocopy] assumes that the input array was created
          locally and will not be used anymore (in the spirit of
          [Bytes.unsafe_to_string]), and avoids a copy of the input
          array when possible. *)
  
      val extend :
        ('a, 'stamp) with_dummy array ->
        length:int ->
        dummy:'stamp dummy ->
        new_capacity:int ->
        ('a, 'stamp) with_dummy array
    end
  end = struct
    (* We want to use a cyclic value so that No_sharing marshalling
       fails loudly, but we want also comparison of dynarrays to work
       as expected, and not loop forever.
  
       Our approach is to use an object value that contains a cycle.
       Objects are compared by their unique id, so comparison is not
       structural and will not loop on the cycle, but marshalled
       by content, so marshalling without sharing will fail on the cycle.
  
       (It is a bit tricky to build an object that does not contain
       functional values where marshalling fails, see [fresh ()] below
       for how we do it.) *)
    type 'stamp dummy = < >
    type fresh_dummy = Fresh : 'stamp dummy -> fresh_dummy
  
    let fresh () =
      (* dummies and marshalling: we intentionally
         use a cyclic value here. *)
      let r = ref None in
      ignore
        (* hack: this primitive is required by the object expression below,
           ensure that 'make depend' notices it. *)
        CamlinternalOO.create_object_opt;
      let dummy = object
        val x = r
      end in
      r := Some dummy;
      Fresh dummy
  
    type ('a, 'stamp) with_dummy = 'a
  
    let of_val v = v
  
    let of_dummy (type a stamp) (dummy : stamp dummy) =
      (Obj.magic dummy : (a, stamp) with_dummy)
  
    let is_dummy v dummy =
      v == of_dummy dummy
  
    let unsafe_get v =
      v
  
    module Array = struct
      let make n x ~dummy =
        if Obj.(tag (repr x) <> double_tag) then
          Array.make n (of_val x)
        else begin
          let arr = Array.make n (of_dummy dummy) in
          Array.fill arr 0 n (of_val x);
          arr
        end
  
      let copy a ~dummy =
        if Obj.(tag (repr a) <> double_array_tag) then
          Array.copy a
        else begin
          let n = Array.length a in
          let arr = Array.make n (of_dummy dummy) in
          for i = 0 to n - 1 do
            Array.unsafe_set arr i
              (of_val (Array.unsafe_get a i));
          done;
          arr
        end
  
      let unsafe_nocopy a ~dummy =
        if Obj.(tag (repr a) <> double_array_tag) then
          a
        else copy a ~dummy
  
      let init n f ~dummy =
        let arr = Array.make n (of_dummy dummy) in
        for i = 0 to n - 1 do
          Array.unsafe_set arr i (of_val (f i))
        done;
        arr
  
      let extend arr ~length ~dummy ~new_capacity =
        (* 'no-flat-float' invariant: we initialise the array with our
           non-float dummy to get a non-flat array. *)
        let new_arr = Array.make new_capacity (of_dummy dummy) in
        Array.blit arr 0 new_arr 0 length;
        new_arr
    end
  end
  
  type 'a t = Pack : ('a, 'stamp) t_ -> 'a t [@@unboxed]
  and ('a, 'stamp) t_ = {
    mutable length : int;
    mutable arr : ('a, 'stamp) Dummy.with_dummy array;
    dummy : 'stamp Dummy.dummy;
  }
  
  let global_dummy = Dummy.fresh ()
  (* We need to ensure that dummies are never exposed to the user as
     values of type ['a]. Including the dummy in the dynarray metadata
     is necessary for marshalling to behave correctly, but there is no
     obligation to create a fresh dummy for each new dynarray, we can
     use a global dummy.
  
     On the other hand, unmarshalling may precisely return a dynarray
     with another dummy: we cannot assume that all dynarrays use this
     global dummy. The existential hiding of the dummy ['stamp]
     parameter helps us to avoid this assumption. *)
  
  module Error = struct
    let[@inline never] index_out_of_bounds f ~i ~length =
      if length = 0 then
        Printf.ksprintf invalid_arg
          "Dynarray.%s: index %d out of bounds (empty dynarray)"
          f i
      else
        Printf.ksprintf invalid_arg
          "Dynarray.%s: index %d out of bounds (0..%d)"
          f i (length - 1)
  
    let[@inline never] negative_length_requested f n =
      Printf.ksprintf invalid_arg
        "Dynarray.%s: negative length %d requested"
        f n
  
    let[@inline never] negative_capacity_requested f n =
      Printf.ksprintf invalid_arg
        "Dynarray.%s: negative capacity %d requested"
        f n
  
    let[@inline never] requested_length_out_of_bounds f requested_length =
      Printf.ksprintf invalid_arg
        "Dynarray.%s: cannot grow to requested length %d (max_array_length is %d)"
        f requested_length Sys.max_array_length
  
    (* When observing an invalid state ([missing_element],
       [invalid_length]), we do not give the name of the calling function
       in the error message, as the error is related to invalid operations
       performed earlier, and not to the callsite of the function
       itself. *)
  
    let invalid_state_description =
      "Invalid dynarray (unsynchronized concurrent length change)"
  
    let[@inline never] missing_element ~i ~length =
      Printf.ksprintf invalid_arg
        "%s: missing element at position %d < length %d"
        invalid_state_description
        i length
  
    let[@inline never] invalid_length ~length ~capacity =
      Printf.ksprintf invalid_arg
        "%s: length %d > capacity %d"
        invalid_state_description
        length capacity
  
    let[@inline never] length_change_during_iteration f ~expected ~observed =
      Printf.ksprintf invalid_arg
        "Dynarray.%s: a length change from %d to %d occurred during iteration"
        f expected observed
  
    (* When an [Empty] element is observed unexpectedly at index [i],
       it may be either an out-of-bounds access or an invalid-state situation
       depending on whether [i <= length]. *)
    let[@inline never] unexpected_empty_element f ~i ~length =
      if i < length then
        missing_element ~i ~length
      else
        index_out_of_bounds f ~i ~length
  
    let[@inline never] empty_dynarray f =
      Printf.ksprintf invalid_arg
        "Dynarray.%s: empty array" f
  end
  
  (* Detecting iterator invalidation.
  
     See {!iter} below for a detailed usage example.
  *)
  let check_same_length f (Pack a) ~length =
    let length_a = a.length in
    if length <> length_a then
      Error.length_change_during_iteration f
        ~expected:length ~observed:length_a
  
  (** Careful unsafe access. *)
  
  (* Postcondition on non-exceptional return:
     [length <= Array.length arr] *)
  let[@inline always] check_valid_length length arr =
    let capacity = Array.length arr in
    if length > capacity then
      Error.invalid_length ~length ~capacity
  
  (* Precondition: [0 <= i < length <= Array.length arr]
  
     This precondition is typically guaranteed by knowing
     [0 <= i < length] and calling [check_valid_length length arr].*)
  let[@inline always] unsafe_get arr ~dummy ~i ~length =
    let v = Array.unsafe_get arr i in
    if Dummy.is_dummy v dummy
    then Error.missing_element ~i ~length
    else Dummy.unsafe_get v
  
  (** {1:dynarrays Dynamic arrays} *)
  
  let create () =
    let Dummy.Fresh dummy = global_dummy in
    Pack {
      length = 0;
      arr = [| |];
      dummy = dummy;
    }
  
  let make n x =
    if n < 0 then Error.negative_length_requested "make" n;
    let Dummy.Fresh dummy = global_dummy in
    let arr = Dummy.Array.make n x ~dummy in
    Pack {
      length = n;
      arr;
      dummy;
    }
  
  let init (type a) n (f : int -> a) : a t =
    if n < 0 then Error.negative_length_requested "init" n;
    let Dummy.Fresh dummy = global_dummy in
    let arr = Dummy.Array.init n f ~dummy in
    Pack {
      length = n;
      arr;
      dummy;
    }
  
  let get (type a) (Pack a : a t) i =
    (* This implementation will propagate an [Invalid_argument] exception
       from array lookup if the index is out of the backing array,
       instead of using our own [Error.index_out_of_bounds]. This is
       allowed by our specification, and more efficient -- no need to
       check that [length a <= capacity a] in the fast path. *)
    let v = a.arr.(i) in
    if Dummy.is_dummy v a.dummy
    then Error.unexpected_empty_element "get" ~i ~length:a.length
    else Dummy.unsafe_get v
  
  let set (Pack a) i x =
    let {arr; length; _} = a in
    if i >= length then Error.index_out_of_bounds "set" ~i ~length
    else arr.(i) <- Dummy.of_val x
  
  let length (Pack a) = a.length
  
  (** {1:removing Removing elements} *)
  
  let pop_last (Pack a) =
    let {arr; length; dummy} = a in
    check_valid_length length arr;
    (* We know [length <= capacity a]. *)
    if length = 0 then raise Not_found;
    let last = length - 1 in
    (* We know [length > 0] so [last >= 0]. *)
    let v = unsafe_get arr ~dummy ~i:last ~length in
    Array.unsafe_set arr last (Dummy.of_dummy dummy);
    a.length <- last;
    v
  
  let next_capacity n =
    let n' =
      (* For large values of n, we use 1.5 as our growth factor.
  
         For smaller values of n, we grow more aggressively to avoid
         reallocating too much when accumulating elements into an empty
         array.
  
         The constants "512 words" and "8 words" below are taken from
           https://github.com/facebook/folly/blob/
             c06c0f41d91daf1a6a5f3fc1cd465302ac260459/folly/FBVector.h#L1128-L1157
      *)
      if n <= 512 then n * 2
      else n + n / 2
    in
    (* jump directly from 0 to 8 *)
    min (max 8 n') Sys.max_array_length
  
  let ensure_capacity (Pack a) capacity_request =
    let arr = a.arr in
    let cur_capacity = Array.length arr in
    if capacity_request < 0 then
      Error.negative_capacity_requested "ensure_capacity" capacity_request
    else if cur_capacity >= capacity_request then
      (* This is the fast path, the code up to here must do as little as
         possible. (This is why we don't use [let {arr; length} = a] as
         usual, the length is not needed in the fast path.)*)
      ()
    else begin
      if capacity_request > Sys.max_array_length then
        Error.requested_length_out_of_bounds "ensure_capacity" capacity_request;
      let new_capacity =
        (* We use either the next exponential-growth strategy,
           or the requested strategy, whichever is bigger.
  
           Compared to only using the exponential-growth strategy, this
           lets us use less memory by avoiding any overshoot whenever
           the capacity request is noticeably larger than the current
           capacity.
  
           Compared to only using the requested capacity, this avoids
           losing the amortized guarantee: we allocated "exponentially
           or more", so the amortization holds. In particular, notice
           that repeated calls to [ensure_capacity a (length a + 1)]
           will have amortized-linear rather than quadratic complexity.
        *)
        max (next_capacity cur_capacity) capacity_request in
      assert (new_capacity > 0);
      let new_arr =
        Dummy.Array.extend arr ~length:a.length ~dummy:a.dummy ~new_capacity in
      a.arr <- new_arr;
      (* postcondition: *)
      assert (0 <= capacity_request);
      assert (capacity_request <= Array.length new_arr);
    end

  let ensure_extra_capacity a extra_capacity_request =
    ensure_capacity a (length a + extra_capacity_request)
  
  let[@inline] add_last_if_room (Pack a) v =
    let {arr; length; _} = a in
    (* we know [0 <= length] *)
    if length >= Array.length arr then false
    else begin
      (* we know [0 <= length < Array.length arr] *)
      a.length <- length + 1;
      Array.unsafe_set arr length (Dummy.of_val v);
      true
    end
  
  let add_last a x =
    if add_last_if_room a x then ()
    else begin
      (* slow path *)
      let rec grow_and_add a x =
        ensure_extra_capacity a 1;
        if not (add_last_if_room a x)
        then grow_and_add a x
      in grow_and_add a x
    end
  
  let of_list li =
    let a = Array.of_list li in
    let length = Array.length a in
    let Dummy.Fresh dummy = global_dummy in
    let arr = Dummy.Array.unsafe_nocopy a ~dummy in
    Pack {
      length;
      arr;
      dummy;
    }
  
  let to_list a =
    let Pack {arr; length; dummy} = a in
    check_valid_length length arr;
    let l = ref [] in
    for i = length - 1 downto 0 do
      l := unsafe_get arr ~dummy ~i ~length :: !l
    done;
    check_same_length "to_list" a ~length;
    !l
end

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

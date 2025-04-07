module Effects

open FStar.All
open FStar.Ref

(* 15 points *)
(* Delete the type [False] and write down the correct spec. You may
   want to separate out the [cache_miss] function to its own definition for
   defining its spec. *)

val memo : False
let memo r f v =
  let cache_miss v =
    let res = f v in
    r := Some (v, res);
    res
  in
  match !r with
  | None -> cache_miss v
  | Some (v', r') ->
      if v = v' then r'
      else cache_miss v

(* Your definition should make the following function type check *)
let test () =
  let foo v = v + 1 in
  let r = alloc None in
  let foo' = memo r foo in

  let r1 = foo 10 in
  let r2 = foo' 10 in
  assert (r1 == r2);
  ()

let test2 () =
  let foo v = v + v in
  let r = alloc None in
  let foo' = memo r foo in

  let r1 = foo 10 in
  let r2 = foo' 10 in
  assert (r1 == r2);
  ()

open FStar.Mul

let rec fact (n : nat) : r:nat{r > 0} =
  if n = 0 then 1 else n * fact (n-1)

(* 10 points *)
(* Write an imperative version of factorial (using a single mutable reference)
   and prove that it satisfies the spec above. *)

let rec tribonacci (n:nat) =
  if n = 0 then 0
  else if n = 1 || n = 2 then 1
  else tribonacci (n-1) + tribonacci (n-2) + tribonacci (n-3)

(* 10 points *)
(* Write an imperative version of tribonacci (using a mutable references)
   and prove that it satisfies the spec above. *)

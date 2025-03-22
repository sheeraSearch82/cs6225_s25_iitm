module PulseIntro
#lang-pulse
open Pulse

let fstar_five : int = 5

(*

Separation Logic Primer
-----------------------

{ P } c { \v. Q }

where `P` and `Q` are separation logic predicates `slprop`s. `slprop` stands for
separation logic predicates.

type slprop = state -> prop

where `state` is the state of the heap.

*)

fn five ()
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  fstar_five
}

let pulse_five_in_fstar = five ()
let pulse_five : int = 5

(*

The above is a convenient way to write

```
{ emp } five () { n:int. pure (n == 5) }.
```

*)

(*

Some simple slprops:
--------------------
* `emp`, the trivial proposition (equivalent to `fun s -> True`).
* `pure p`, heap-independent predicate `fun s -> p`.
   + `emp` is equivalent to `pure True`.

Ownership and permission
------------------------
* Key idea is the concept of ownership.
  + A computation can only access those resources that it is explicitly granted
    access to in its precondition or those that it creates itself.
  + `five` cannot access any resources, because its precondition is `emp`.
    - This is different from ST effect in F*. See `incr` in
      `PureIntroSupport.fst`.
*)

(* UNCOMMENT AND EXPECT FAILURE *)
(*
fn five' (x : ref int)
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  let v = !x;
  x := v + 1;
  fstar_five
}
*)

fn incr (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}

(*

Separation Logic Rules
----------------------

## Connectives in Separation Logic

Connectives of separation logic in terms of the sets of partial
heaps that they accept.

(1) emp = {●}
(2) pts_to x v = {●[x -> v]}
(3) pure P = {h | P /\ h = ●}
(3) exists x. P = {h | exists x. h ∈ P(x)}
(4) P ** Q = {h1 ⨄ h2 | h1 ∈ P /\ h2 ∈ Q}
(5) p @==> q = {h | h ∈ p ==> h ∈ q}

## Properties

* Commutative : P ** Q @==> Q ** P
* Associative : P ** (Q ** R) @==> (P ** Q) ** R
* Idempotent  : P ** emp @==> P
* Frame rule  :

       {P} c {Q}
  -------------------
  {P ** R} c {Q ** R}

  + Captures the essence of local modular reasoning
  + If a program is correct with permission `P` then it is correct in a larger
    context with additional permissions `R` which it doesn't touch.

*)

(* Thanks to the frame rule, the following need not mention anything about `y`.
   This is not true with ST effect in F*. See `incr3` in
   `PulseIntroSupport.fst` *)

fn incr_frame (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y 'j
{
   incr x;
}

(* In fact, Pulse lets us use the frame rule with any `f:slprop`, and we get,
   for free, that `incr x` does not disturb `f`. *)

fn incr_frame_any (x:ref int) (f:slprop)
requires pts_to x 'i ** f
ensures pts_to x ('i + 1) ** f
{
   incr x;
}
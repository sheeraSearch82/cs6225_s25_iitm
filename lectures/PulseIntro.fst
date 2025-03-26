module PulseIntro
#lang-pulse
open Pulse

(******************************************************************************)
(* Section: Pulse Basics *)
(******************************************************************************)

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

[@@expect_failure]
fn five' (x : ref int)
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  let v = !x;
  x := v + 1;
  fstar_five
}

fn incr (x:ref int)
requires pts_to x 'i (* implicitly bound logical variable *)
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}

fn incr_explicit_i (x:ref int) (i:erased int)
requires pts_to x i (* explicitly bound logical variable *)
ensures pts_to x (i + 1)
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

(******************************************************************************)
(* Section: Mutable References *)
(******************************************************************************)

(*

* Aim to have memory management without GC
  + Be able to target C or Rust
* Different kinds of references
  + Stack, Heap and Ghost

*)

(* [ref t] type is agnostic to whether it is in heap or stack. Comes from
   [Pulse.Lib.Reference.ref t] *)

fn swap #a (r0 r1:ref a)
requires pts_to r0 'v0 ** pts_to r1 'v1
ensures pts_to r0 'v1 ** pts_to r1 'v0
{
    let v0 = !r0;
    let v1 = !r1;
    r0 := v1;
    r1 := v0;
}

(* Reading a reference *)

fn value_of (#a:Type) (r:ref a)
requires pts_to r 'v
returns v:a
ensures pts_to r 'v ** pure (v == 'v)
{
    !r;
}

fn value_of_explicit (#a:Type) (r:ref a) (#w:erased a)
requires pts_to r w
returns v:a
ensures pts_to r w ** pure (v == reveal w)
{
    !r;
}

[@@expect_failure]
fn value_of_explicit_fail (#a:Type) (r:ref a) (#w:erased a)
requires pts_to r w
returns v:a
ensures pts_to r w ** pure (v == reveal w)
{
    reveal w (* cannot use erased values in non-ghost computations *)
}

(* Writing to a reference *)

fn assign (#a:Type) (r:ref a) (v:a)
requires pts_to r 'v
ensures pts_to r v
{
    r := v;
}

fn add (r:ref int) (n:int)
requires pts_to r 'v
ensures pts_to r ('v + n)
{
    let v = !r;
    r := v + n;
}

open FStar.Mul

fn quadruple (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r;
    add r v1;
    let v2 = !r;
    add r v2;
}

(* Pulse type checking has two components)
   1. Typing environment
   2. `slprop` context (or context for short)

   If {p ** q} goal {r ** q} holds and {p} goal {r} also holds, then we call [p]
   the "support" of [goal] and [q] the "frame" of [goal].
*)

[@@expect_failure] //comment this line to see the output of [show_proof_state]
fn quadruple' (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r; // Env=v1:int; _:squash (v1 == 'v)       Ctxt= pts_to r v1
    add r v1;    // ...                                   Ctxt= pts_to r (v1 + v1)
    show_proof_state;
    let v2 = !r; // Env=...; v2:int; _:squash(v2==v1+v1)  Ctxt= pts_to r v2
    add r v2;    // Env=...                               Ctxt= pts_to r (v2 + v2)
                 // ..                                    Ctxt= pts_to r (4 * 'v)
    show_proof_state;

}

[@@expect_failure] //Stateful commands are explicitly sequenced
fn quad_fail (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    add r (!r);
    add r (!r);
}

(* Fractional Permissions *)

(* Actual type of [pts_to]) is:

   val pts_to (#a:Type u#0) (r:ref a) (#p:perm) (v:a) : vprop

  The [perm] argument is interesting.
  * 1.0R default
  * 0.0R < p <= 1.0R
  * Write requires 1.0R
  * Read can be done at any value of perm.
*)

fn assign_full_perm (#a:Type) (r:ref a) (v:a)
requires pts_to r #1.0R 'v
ensures pts_to r #1.0R v
{
    r := v;
}

fn value_of_perm #a #p (r:ref a)
requires pts_to r #p 'v
returns v:a
ensures pts_to r #p 'v ** pure (v == 'v)
{
    !r;
}

#push-options "--print_implicits"
[@@expect_failure]
fn assign_perm #a #p (r:ref a) (v:a) (#w:erased a)
requires pts_to r #p w
ensures pts_to r #p w
{
    r := v;
}
#pop-options

fn share_ref #a #p (r:ref a)
requires pts_to r #p 'v
ensures pts_to r #(p /. 2.0R) 'v ** pts_to r #(p /. 2.0R) 'v
{
    share r;
}

fn gather_ref #a (#p:perm) (r:ref a)
requires
    pts_to r #(p /. 2.0R) 'v0 **
    pts_to r #(p /. 2.0R) 'v1
ensures
    pts_to r #p 'v0 **
    pure ('v0 == 'v1) //pointed-to witnesses are equal
{
    gather r
}

(* [let mut] creates a new stack ref *)
fn one ()
requires emp
returns v:int
ensures pure (v == 1)
{
                   //     .     |- emp
    let mut i = 0; // i:ref int |- pts_to i 0
    incr i;        // i:ref int |- pts_to i (0 + 1)
    !i             //      .    |- v:int. emp ** pure (v == 1)
}

[@@expect_failure]
fn refs_are_scoped ()
requires emp
returns s:ref int
ensures pts_to s 0
{
    let mut s = 0;
    s
}

module Box = Pulse.Lib.Box
(* For heap references. Like Rust's Box<T>. Box has the functions pts_to, (!),
   (:=), share, gather, alloc and free. *)

fn new_heap_ref (#a:Type) (v:a)
requires emp
returns r:Box.box a
ensures Box.pts_to r v
{
    Box.alloc v
}

fn last_value_of #a (r:Box.box a)
requires Box.pts_to r 'v
returns v:a
ensures pure (v == 'v)
{
    open Box;
    let v = !r;
    free r;
    v
}

(* [box t] references can be demoted to regular [ref t] references for code
   reuse. *)
fn incr_box (r:Box.box int)
requires Box.pts_to r 'v
ensures Box.pts_to r ('v + 1)
{
    Box.to_ref_pts_to r;     //pts_to (box_to_ref r) 'v
    incr (Box.box_to_ref r); //pts_to (box_to_ref r) ('v + 1)
    Box.to_box_pts_to r      //Box.pts_to r ('v + 1)
}

(******************************************************************************)
(* Section: Existential quantification *)
(******************************************************************************)

(* Examples: [exists*] is an [slprop -> slprop] constructor.

- exists* (v:nat). pts_to x v
- exists* v. pts_to x v
- exists* v1 v2. pts_to x v1 ** pts_to y v2

*)

fn assign2 (#a:Type) (r:ref a) (v:a)
requires pts_to r 'v //why bother binding this?
ensures pts_to r v
{
    r := v;
}

fn assign2' #a (x:ref a) (v:a)
requires
  exists* w. pts_to x w
ensures
  pts_to x v
{
  x := v
}

[@@expect_failure]
fn incr #a (x:ref int)
requires
  exists* w0. pts_to x w
ensures
  pts_to x (w0 + 1) //w0 is not in scope here
{
  let w = !x
  x := w + 1
}

(* Existential quantification often appears in postconditions, e.g., in order to
   abstract the behavior of function by underspecifying it. *)

fn make_even (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  let v = !x;
  x := v + v;
}

(* Manipulating existentials

   F* automatically manipulates existentials. But sometimes it is useful to know
   how to manage them explicitly.

  [with w0...wn. assert p; rest] eliminates existentials when the context
   contains [exists* x0...xn. p].

   [with] construct binds [w0...wn] to the existentially quantified variables
   [x0...xn] in the remainder of the scope [rest]. *)


fn make_even_explicit (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  //show_proof_state;
  with w0. assert (pts_to x w0);
  //show_proof_state;
  let v = !x; // v:int; _:squash(v==w0); Ctxt=pts_to x v
  x := v + v; //                          ... pts_to x (v + v)
  //show_proof_state;
  introduce
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
  with (v + v);
  //show_proof_state;
}

(* [introduce exists* x1..xn. p with w1..wn] introduces existentials [x1..xn] in
   the context with witnesses [w1..wn] *)

(* When there is a single existential formula in the context, one can write with
   [x1..xn. _] to "open" the formula, binding its witnesses in scope. *)
fn make_even_explicit_alt (x y:ref int)
requires
  exists* wx wy. pts_to x wx ** pts_to y wy ** pure (wx % 2 == wy % 2)
ensures
  exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
{
  //show_proof_state;
  with wx wy. _;
  //show_proof_state;
  let vx = !x;
  let vy = !y;
  x := vx + vy;
  introduce exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
  with (vx + vy) vy;
}


(******************************************************************************)
(* Section: User-defined Predicates *)
(******************************************************************************)

let pts_to_diag
        #a
        (r:ref (a & a))
        (v:a)
: slprop
= pts_to r (v, v)

fn double (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold (pts_to_diag r 'v); //What is [unfold]?
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  //show_proof_state;
  fold (pts_to_diag r v2); //What is [fold]?
}

fn double_alt (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold pts_to_diag;
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold pts_to_diag;
}

(* Mutable points *)

noeq
type point = {
    x:ref int;
    y:ref int;
}

//[is_point] is a "representation predicate" for [point] type.
let is_point (p:point) (xy: int & int) =
    pts_to p.x (fst xy) **
    pts_to p.y (snd xy)

fn move (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  //show_proof_state;
  fold (is_point p (x + dx, y + dy));
    //Pulse cannot infer the instantiation of [is_point] when folding it.
}

ghost
fn fold_is_point (p:point)
requires pts_to p.x 'x ** pts_to p.y 'y
ensures is_point p (reveal 'x, reveal 'y)
{
  fold (is_point p (reveal 'x, reveal 'y))
}

fn move_alt (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold_is_point p;
}

(* Rewriting

    with x1 ... xn. rewrite p as q;
    rest

*)

fn create_and_move ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    //pts_to x 0 ** pts_to y 0
    with _v. rewrite pts_to x _v as pts_to p.x _v;
    with _v. rewrite pts_to y _v as pts_to p.y _v;
    //pts_to p.x 0 ** pts_to p.y 0
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    //pts_to p.x (fst (1, 1)) ** pts_to p.y (snd (1, 1))
    with _v. rewrite pts_to p.x _v as pts_to x _v;
    with _v. rewrite pts_to p.y _v as pts_to y _v;
    //pts_to x (fst (1, 1)) ** pts_to y (snd (1, 1))
}

fn create_and_move_alt ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    rewrite each
      x as p.x, y as p.y;
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    rewrite each
      p.x as x, p.y as y;
}
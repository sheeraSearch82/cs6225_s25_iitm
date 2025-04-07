module Pulsating
#lang-pulse
open Pulse
open Pulse.Lib.Pervasives

(******************************************************************************)
(* Swap3 (5 points) *)
(******************************************************************************)
(* The following shows a pulse [swap] function that swaps the values of two
   references. Implement a [swap3] function that swaps the values of three
   references [r1], [r2], and [r3]. The function should swap the values in such
   a way that [r1] gets the value of [r3], [r2] gets the value of [r1], and [r3]
   gets the value of [r2]. *)

fn swap #a (r1:ref a) (r2:ref a)
requires pts_to r1 'v1 ** pts_to r2 'v2
ensures pts_to r1 'v2 ** pts_to r2 'v1
{
  let v1 = !r1;
  let v2 = !r2;
  r2 := v1;
  r1 := v2
}

(******************************************************************************)
(* Mutable Tribonacci (10 points) *)
(******************************************************************************)

(* We have seen the mutable implementation of Fibonacci in the FStar effects
   lecture where we proved that it satisfies the functional specification.
   Similarly, we have seen Fibonacci implementation in Pulse. Implement a Pulse
   version of Tribonacci numbers, and prove it correct according to the spec
   below: *)

let rec tribonacci (n:nat) : nat =
  if n = 0 then 0
  else if n = 1 then 0
  else if n = 2 then 1
  else tribonacci (n - 1) + tribonacci (n - 2) + tribonacci (n - 3)

(* You will need to use 3 mutable references *)
fn trib_mut (n:nat)
requires emp
returns r:nat
ensures pure (tribonacci n = r)
{
  admit ();
}

(******************************************************************************)
(* Array.find (20 points) *)
(******************************************************************************)

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open FStar.SizeT
open Pulse.Lib.BoundedIntegers


(* You can see the implementation of a [Array.fill] function below for
   reference. *)

fn fill (#t:Type0) (l:SZ.t) (a:larray t (SZ.v l)) (v:t)
  requires pts_to a 's
  ensures exists* (s:Seq.seq t).
    pts_to a s **
    pure (s `Seq.equal` Seq.create (SZ.v l) v)
{
  pts_to_len a #1.0R #'s;
  let mut i = 0sz;
  while (let vi = !i; (vi < l))
  invariant b. exists* (vi:SZ.t) (s:Seq.seq t). (
    pts_to i vi **
    pts_to a s **
    pure (vi <= l
        /\ Seq.length s == SZ.v l
        /\ (b == (vi < l))
        /\ (forall (i:nat). i < SZ.v vi ==> Seq.index s i == v)))
  {
    let vi = !i;
    (a.(vi) <- v);
    i := vi + 1sz;
  }
}

(* Your job is to implement an [Array.find] function that satisfies the
   following signature. *)

fn find (#t:Type0) (l:SZ.t) (p:t->bool) (a:array t) (#s:erased (Seq.seq t))
requires
  pts_to a s **
  pure (Seq.length s == SZ.v l)
returns r:bool
ensures
  (pts_to a s **
  pure (Seq.length s == SZ.v l
        /\ (r <==> exists (i:nat). i < SZ.v l /\ p (Seq.index s i))))
{
  admit ();
}


(******************************************************************************)
(* List reverse (20 points) *)
(******************************************************************************)

(* Write a function in Pulse that reverses a linked list, and show that it is
   correct. The list definition and the helper functions from the lecture are
   given below. *)

noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)

(* Representation predicate linking linked list to logic representation *)
let rec is_list #t (x:llist t) (l:list t)
: Tot slprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl ->
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl

(* Some boilerplate. TODO: Pulse will automate later. *)

ghost
fn elim_is_list_nil (#t:Type0) (x:llist t)
requires is_list x 'l ** pure ('l == [])
ensures pure (x == None)
{
   rewrite each 'l as Nil #t;
   unfold (is_list x [])
}

ghost
fn intro_is_list_nil (#t:Type0) (x:llist t)
requires pure (x == None)
ensures is_list x []
{
    fold (is_list x []);
}

ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (l:list t) (head:t) (tl:list t)
requires is_list x l ** pure (l == head::tl)
ensures (
  exists* (p:node_ptr t) (tail:llist t).
    pure (x == Some p) **
    pts_to p { head; tail } **
    is_list tail tl
)
{
  rewrite each l as (head::tl);
  unfold (is_list x (head::tl));
}

ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t)
                      (#node:node t) (#tl:list t)
requires
  pts_to v node **
  is_list node.tail tl **
  pure (x == Some v)
ensures
  is_list x (node.head::tl)
{
    rewrite (pts_to v node) as (pts_to v { head=node.head; tail=node.tail });
    fold (is_list x (node.head::tl));
}

(* Case analyzing a nullable pointer a.k.a more helper functions *)

let is_list_cases #t (x:llist t) (l:list t)
: slprop
= match x with
  | None -> pure (l == [])
  | Some v ->
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl

ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  match l {
    Nil -> {
      unfold (is_list x []);
      fold (is_list_cases None l);
      rewrite each (None #(ref (node t))) as x; //can be commented out?
    }
    Cons head tl -> {
      unfold (is_list x (head::tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
      fold (is_list_cases (Some v) l);
      //show_proof_state;
      rewrite each (Some #(ref (node t)) v) as x;
    }
  }
}

ghost
fn is_list_case_none (#t:Type) (x:llist t) (#l:list t)
requires is_list x l ** pure (x == None)
ensures is_list x l ** pure (l == [])
{
  cases_of_is_list x l;
  rewrite each x as (None #(ref (node t)));
  unfold (is_list_cases None l);
  fold (is_list x []);
}

ghost
fn is_list_case_some (#t:Type) (x:llist t) (v:node_ptr t) (#l:list t)
requires is_list x l ** pure (x == Some v)
ensures
  exists* (node:node t) (tl:list t).
    pts_to v node **
    is_list node.tail tl **
    pure (l == node.head::tl)
{
  cases_of_is_list x l;
  rewrite each x as (Some v);
  unfold (is_list_cases (Some v) l);
}
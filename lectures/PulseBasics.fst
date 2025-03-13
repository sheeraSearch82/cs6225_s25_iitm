module PulseBasics

#lang-pulse

open Pulse.Lib.Pervasives

(*  Separation Logic Primer *)
(* -----------------------------------------------------------------------------------------*)
(* --- Separation Logic Propositions --- *)
 (* The language of propositions that describe properties about program resources, e.g., the heap. 
    have the type slprop in Pulse*)
 
 (* slprop = state -> prop, 
    where state represents the state of a program, e.g., the contents of memory. 
    slprops is defined in Pulse.Lib.Pervasives
    pure p, heap-independent predicate fun s -> p. emp is equivalent to pure True.
    *** NOTE *** In the tutorial vprop is used instead of slprop. slprop is the updated name.
 *)

 (* --- Separation Logic Hoare Triples --- *)
 (* To connect slprop’s to programs, separation logics use Hoare triples to describe the action of a program on its state. 
    For example, the Hoare triple { p } c { n. q } describes a program 
    p ---> pre-condition that is true on initial state s0
    c ---> a program
    n ---> return value of c 
    q ---> post-condition on the final state s1. 
  *)

 (* Simple slprops and triples*)
 (* 1. emp, the trivial proposition (equivalent to fun s -> True)
    2. pure p, heap-independent predicate fun s -> p. emp is equivalent to pure True.*)

let fstar_five : int = 5

```pulse
fn five ()
  requires emp
  returns n:int
  ensures pure (n == 5)
{ 
  fstar_five
}
```
(* pulse functions are embedded between ```pulse and ```*)
(* A pulse function begins with the keyword fn *)

(* The above Pulse program does not cause any change in the memory state. It can work in any initial state, as indicated by emp. 
   It returns an integer n with value 5. pure indicates that the 
   memory is unchanged.*)

(* Hoare triple corresponding to the above pulse function is, { emp } five () { n:int. pure (n == 5) }. *)

let pulse_five_in_fstar = five ()

(* The above F* function calls the pulse function five ()*)

(* The above example shows the to and fro operations or interoperability of F* and Pulse*)

(* ---- Ownership - very important concept ----*)

(* Questions
   ---------
   Does the post-condition of five () is strong enough?
   Does five () modifies memory state?
   How can we ensure that?
   pure (5 == 5) is true in memory state, so how can we ensure that the initial memory state is not modified due to five ()?

   Answer
   --------
   The answer is the memory state is unchanged due to five (). Reason is due to a central concept in logic called Ownership.
   That is, a computation can only access those resources that are explicitly granted access to the computation in its precondition.
   emp states that five () is not given access permission to any resource. Hence five () cannot alter any resource. Thus proving
   that the initial memory state and final memory state are the same.

  
(* ---Separating Conjunction and the Frame Rule --- *)
(* Another example of a slprop is the slprop that starts with the pts_to predicate as follows:
   pts_to x v - asserts that the reference x points to a cell in the current state that holds the value v *)

   Separating Conjunction
   -----------------------
   ** - Called as separating conjunction, used to combine slprops
   p ** q, means that the state can be split into two disjoint fragments satisfying p and q, respectively. 
   Alternatively, one could read p ** q as meaning that one holds the permissions associated with both p and q separately 
   in a given state. 
   
   The ** operator satisfies the following laws:
       ( 1 ) Commutativity: p ** q is equivalent to q ** p
       ( 2 ) Associativity: p ** (q ** r) is equivalent to (p ** q) ** r
       ( 3 ) Left and right unit: p ** emp is equivalent to p. 
             Since ** is commutative, this also means that emp ** p is equivalent to p
   
   frame rule 
   ------------------------
   - Captures the essence of local, modular reasoning.
   -  The rule says thatif we can prove the Hoare triple, { p } c { n. q }, then for any other f:slprop, we can also prove
      { p ** f } c { n. q ** f }
   
   It states that if a program c is correct when it only has permission p on the input state, 
   then it remains correct when run in a larger state and is guaranteed to preserve 
   any property (f) on the part of the state that it doesn’t touch.

        { p } c { n. q }
   --------------------------
   { p ** f } c { n. q ** f }, where f is the frame.*)


(* -----------------------------------------------------------------------------------------*)

(* Pulse Basics *)
(* -----------------------------------------------------------------------------------------*)
(* A first taste of Pulse program that incorporates some of the above concepts *)
(* incr takes as argument a reference to an integer, called x *)
(* pts_to means x 'i means x points to the value 'i. Note the use of '. This means 'i is implicit.
  We don't need to i explicitly *)
(* The pre-condition says that x points to 'i *)
(* The post-condition says that x points to ('i + 1) *)
(* let let v = !x; means v gets the value stored at x *)
(*  x := v + 1; means x is updated with v + 1*)
fn incr (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}


fn par_incr (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
  par (fun _ -> incr x )
      (fun _ -> incr y)
}

(* Due to frame rule, we can prove that y is unchanged.*)
fn incr_frame (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y 'j
{
   incr x;
}

(* This is true for any general f:slprop. We therefore get the post-condition that incr does not alter f, for free*)
(* 'i - 'i has type FStar.Ghost.erased int*)
fn incr_frame_any (x:ref int) (f:slprop)
requires pts_to x 'i ** f
ensures pts_to x ('i + 1) ** f
{
   incr x;
}

(* Explicit way of passing the value in ref cell x. Note the use of erased *)

fn incr_explicit_i (x:ref int) (i:erased int)
requires pts_to x i
ensures pts_to x (i + 1)
{
    let v = !x;
    x := v + 1;
}

(* Other slprop connectives
   1. exists* (x1:t1) ... (xn:tn). p 
   2. forall* (x1:t1) ... (xn:tn). p 
   3. p @==> q - , called separating implication. Similar to magic wand or view shift in other Separation logics.*)

(* TODO - Examples will be provided later *)

(* MUTABLE REFERENCES*)


(*--ref t ----> Stack or Heap references --*)

(* Reading a reference *)


(* Erased values - for specifications and proofs only *)

(* Writing through a reference *)

(* Dereferencing is explicit *)

(* Inspecting the Proof state *)

(* Stateful commands are explicitly sequenced *)

(* Fractional permissions *)

(* STACK REFERENCES *)

(* Stack references are scoped and implicitly reclaimed *)

(* HEAP REFERENCES *)

(* GHOST REFERENCES*)




(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)


module PulseTutorial.LinkedList
#lang-pulse
open Pulse.Lib.Pervasives
module FA = Pulse.Lib.Forall.Util
//open FStar.List.Tot
module L = FStar.List.Tot


//llist$
noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)
//end llist$

//is_list$
let rec is_list #t (x:llist t) (l:list t)
: Tot slprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl -> 
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl
//end is_list$

//boilerplate$

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
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t) (#node:node t) (#tl:list t)
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

//end boilerplate$

//is_list_cases$
let is_list_cases #t (x:llist t) (l:list t)
: slprop 
= match x with
  | None -> pure (l == [])
  | Some v -> 
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl
//end is_list_cases$

//cases_of_is_list$
ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  (*match l {
    [] -> {
      unfold (is_list x []);
      fold (is_list_cases None l);
      rewrite each (None #(ref (node t))) as x;
    }
    head :: tl -> {
      unfold (is_list x (head::tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
      fold (is_list_cases (Some v) l);
      rewrite each (Some #(ref (node t)) v) as x;
    }
  }*)
  admit()
}
//end cases_of_is_list$


//is_list_case_none$
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
//end is_list_case_none$


//is_list_case_some$
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
//end is_list_case_some$


(* val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl
  *)

//length$
fn rec length (#t:Type0) (x:llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  match x {
    None -> {
      is_list_case_none x;
      0
    }
    Some vl -> {
      is_list_case_some x vl;
      let node = !vl;
      let n = length node.tail;
      intro_is_list_cons x vl;
      (1 + n)
    }
  }
}
//end length$

(* val rev_acc: list 'a -> list 'a -> Tot (list 'a)
let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc) *)

//length_tail$
fn rec length_tail (#t:Type0) (x:llist t) (k:nat)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == k + List.Tot.length 'l)
{
  match x {
    None -> {
      is_list_case_none x;
      k
    }
    Some vl -> {
      is_list_case_some x vl;
      with _node _tl. _;
      let n = !vl;
      rewrite each _node as n;
      let n = length_tail n.tail (1 + k);
      intro_is_list_cons x vl;
      n
    }
  }
}
//end length_tail$



//append$
fn rec append (#t:Type0) (x y:llist t)
requires is_list x 'l1 ** is_list y 'l2 ** pure (Some? x)
ensures is_list x ('l1 @ 'l2) ** pure (Some? x)
{
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  let node = !np;
  rewrite each _node as node;
  match node.tail {
    (* tail of x can be empty or non-empty *)
    (* If empty, that is the point of appending *)
    None -> {
      (* requires is_list x l ** pure (x == None)
         ensures is_list x l ** pure (l == []) *)
      is_list_case_none None;

      (* requires is_list x 'l ** pure ('l == [])
         ensures pure (x == None) *)

      elim_is_list_nil None;
      np := { node with tail = y };
      rewrite each y as ({ node with tail = y }).tail in (is_list y 'l2);

      (* requires
              pts_to v node **
              is_list node.tail tl **
              pure (x == Some v)
         ensures
              is_list x (node.head::tl) *)
      intro_is_list_cons x np; 
    }
    Some _ -> {
      append node.tail y;
      intro_is_list_cons x np;
    }
  }
}

//end append$

val rev_acc: list 'a -> list 'a -> Tot (list 'a)

let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

val rev: list 'a -> Tot (list 'a)

let rec rev l  = match l with
    | [] -> []
    | [x] -> [x]
    | hd::tl -> List.Tot.append (rev tl) (hd::[])

(* l = [1,2,3] 
   tl l = [2,3]
   rev tl = [3,2]
   append (rev tl) (hd::[]) =
   append [3,2] (1:[]) =
   [3,2,1]
   *)





module Box = Pulse.Lib.Box

//open Pulse.Lib.Box { box, (:=), (!) }


let null_llist #t : llist t = None #(node_ptr t)

fn create (t:Type)
    requires emp
    returns x:llist t
    ensures is_list x []
{
    fold (is_list null_llist ([] <: list t));
    null_llist #t
}



fn cons (#t:Type) (v:t) (x:llist t)
    requires is_list x 'l
    returns y:llist t
    ensures is_list y (v::'l) ** pure (Some? y)
{
    let y = alloc { head=v; tail=x };
    rewrite each x as ({head=v; tail=x}).tail in (is_list x 'l);
    fold (is_list (Some y) (v::'l));
    Some y
}


fn rec reverse (#t:Type0) (x:llist t)
requires is_list x 'l1
returns y:llist t
ensures is_list y  (rev 'l1) ** (pure (Some? x ==> Some? y))
{
   match x {
    None -> {
      //is_list_case_none x;
      let y = create t;
      elim_is_list_nil y;
      is_list_case_none y;
      y
      
    }
    Some vl -> {
      let np = Some?.v x;
      is_list_case_some x np;
      with _node _tl. _;
      let node = !np;
      rewrite each _node as node;
      let empty = create t;
      let hd_lst = cons node.head empty;
      match node.tail 
      {
        None -> {
          is_list_case_none None;
          elim_is_list_nil None;
          free np;
          hd_lst
      }
        Some vlr -> {
         let rev_tl = reverse node.tail;
         //_assume (Some? rev_tl);
         append rev_tl hd_lst;
         free np;
         rev_tl
         
    }
   }
  }
 }
}


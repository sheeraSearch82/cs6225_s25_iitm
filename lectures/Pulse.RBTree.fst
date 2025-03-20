module Pulse.RBTree

(*
 * Red black trees, and verification of Okasaki's insertion algorithm
 * (https://wiki.rice.edu/confluence/download/attachments/2761212/Okasaki-Red-Black.pdf)
 *)

(* CH: how does this compare to Andrew Appel's verified RB-trees?
   http://www.cs.princeton.edu/~appel/papers/redblack.pdf
*)

(* color: Red or Black *)
type color =
  | R
  | B

(*
 * tree data type
 * either empty (E), or a node with a color, left child, key, and a right child
 *)
type rbtree' =
  | E
  | T: col:color -> left:rbtree' -> key:nat -> right:rbtree' -> rbtree'

val color_of: t:rbtree' -> Tot color
let color_of t = match t with
  | E -> B
  | T c _ _ _ -> c

(*
 * this calculates the black height of the tree
 * ensures that black height of all the leaves is same
 * if not, returns None, else returns the black height
 *)
val black_height: t:rbtree' -> Tot (option nat)
let rec black_height t = match t with
  | E -> Some 0
  | T c a _ b ->
    (*
     * TODO: ideally we should be able to write match (black_height a, black_height b)
     *)
    let hha = black_height a in
    let hhb = black_height b in
    match (hha, hhb) with
      | Some ha, Some hb ->
        if ha = hb then
          if c = R then Some ha else Some (ha + 1)
        else
          None
      | _, _ -> None

(* returns the minimum element in a T tree (E tree has no element) *)
val min_elt: t:rbtree' -> Pure nat (requires (b2t (T? t))) (ensures (fun r -> True))
let rec min_elt (T _ a x _) = match a with
  | E -> x
  | _ -> min_elt a

(* returns the maximum element in a T tree *)
val max_elt: t:rbtree' -> Pure nat (requires (b2t (T? t))) (ensures (fun r -> True))
let rec max_elt (T _ _ x b) = match b with
  | E -> x
  | _ -> max_elt b

(*
 * in a red black tree, root of the tree must be black
 *)
val r_inv: t:rbtree' -> Tot bool
let r_inv t = color_of t = B

(*
 * in a red black tree, every red node must have black children
 *)
val c_inv: t:rbtree' -> Tot bool
let rec c_inv t = match t with
  | E -> true
  | T R a _ b -> color_of a = B && color_of b = B && c_inv a && c_inv b
  | T B a _ b -> c_inv a && c_inv b

(*
 * in a red black tree, black height of every leaf must be same
 *)
val h_inv: t:rbtree' -> Tot bool
let h_inv t = Some? (black_height t)

(*
 * finally, this is the binary search tree invariant
 * i.e. all elements in the left subtree are smaller than the root key
 * and all elements in the right subtree are greater than the root key
 *)
val k_inv: t:rbtree' -> Tot bool
let rec k_inv t = match t with
  | E -> true
  | T _ E x E -> true
  | T _ E x b  ->
    let b_min = min_elt b in
    k_inv b && b_min > x
  | T _ a x E ->
    let a_max = max_elt a in
    k_inv a && x > a_max
  | T _ a x b ->
    let a_max = max_elt a in
    let b_min = min_elt b in
    k_inv a && k_inv b && x > a_max && b_min > x

val in_tree: t:rbtree' -> k:nat -> Tot bool
let rec in_tree t k = match t with
  | E -> false
  | T _ a x b -> in_tree a k || k = x || in_tree b k
(* TODO: should try to make it (verify insert) using following code for in_tree *)
(*if k < x then
      in_tree a k
    else if k = x then
      true
    else
      in_tree b k*)

(*
 * Okasaki's insertion algorithm inserts the element at its bst place
 * in a red node, and then uses a balance function to re-establish
 * the red black tree invariants.
 *
 * not_c_inv represents violation of c_inv property, i.e. when a red node
 * may have a red child either on left branch or right branch.
 *)
type not_c_inv (t:rbtree') =
    (T? t) /\ (T?.col t = R) /\ (((T? (T?.left t) /\ T?.col (T?.left t) = R)) \/
                                  ((T? (T?.right t) /\ T?.col (T?.right t) = R)))

(*
 * in Okasaki's algorithm the re-establishment of invariants takes place
 * bottom up, meaning although the invariants may be violated at top,
 * the subtrees still satisfy c_inv.
 *)
type lr_c_inv (t:rbtree') = T? t /\ c_inv (T?.left t) /\ c_inv (T?.right t)

(*
 * this is the predicate satisfied by a tree before call to balance
 *)
type pre_balance (c:color) (lt:rbtree') (ky:nat) (rt:rbtree') =
    (*
     * lt satisfies k_inv, rt satisfies k_inv, and key is a candidate root key for
     * a tree with lt as left branch and rt as right.
     *)
    (
    k_inv lt /\ k_inv rt /\
    (E? lt \/ (T? lt /\ ky > (max_elt lt))) /\
    (E? rt \/ (T? rt /\ (min_elt rt) > ky))
    )

    /\

    (*
     * lt and rt satisfy h_inv, moreover, their black heights is same.
     * the second condition ensures that if resulting tree has (lt k rt), it
     * satisfies h_inv
     *)
    (h_inv lt /\ h_inv rt /\ Some?.v (black_height lt) = Some?.v (black_height rt))

    /\

    (*
     * either lt and rt satisfy c_inv (in which case c can be R or B)
     * or if they don't satisfy c_inv, c has to be B. this is a property
     * ensures by Okasaki's algorithm. Following is basically a formula for
     * cases in Fig. 1 of Okasaki's paper.
     *)

    (
    (c = B /\ not_c_inv lt /\ lr_c_inv lt /\ c_inv rt) \/
    (c = B /\ not_c_inv rt /\ lr_c_inv rt /\ c_inv lt) \/
    (c_inv lt /\ c_inv rt)
    )

type post_balance (c:color) (lt:rbtree') (ky:nat) (rt:rbtree') (r:rbtree') =
              (* TODO: this should come from requires *)
              Some? (black_height lt) /\

              (* returned tree is a T tree *)
              (T? r) /\

              (*
               * returned tree satisfies k_inv
               * in addition, either lt is E and ky is min elt in r OR
               * min elt in returned tree is same as min elt in lt
               * (resp. for max elt and rt)
               *)
              (k_inv r /\
              ((E? lt /\ min_elt r = ky) \/ (T? lt /\ min_elt r = min_elt lt)) /\
              ((E? rt /\ max_elt r = ky) \/ (T? rt /\ max_elt r = max_elt rt))) /\

              (*
               * returned tree satisfies h_inv
               * in addition, black height of returned tree is either same as or
               * one more than lt (and hence rt) depending on c = R or c = B
               *)

              ((h_inv r) /\
              ((c = B /\ Some?.v(black_height r) = Some?.v(black_height lt) + 1) \/
               (c = R /\ Some?.v(black_height r) = Some?.v(black_height lt)))) /\

              (*
               * returned tree either satisfies c_inv OR
               * if it doesn't, it must be the case that c (and hence T?.col r) = R
               *)
              (c_inv r  \/
              (T?.col r = R /\ c = R /\ not_c_inv r /\ lr_c_inv r)) /\

              (*
               * resulting tree contains all elements from lt, ly, and rt, and
               * nothing else
               *)
              (forall k. in_tree r k <==> (in_tree lt k \/ k = ky \/ in_tree rt k))

(*
 * balance function
 * similar to pre_balance, post condition specifies invariants for
 * k_inv, h_inv, and c_inv
 *)
val balance: c:color -> lt:rbtree' -> ky:nat -> rt:rbtree' ->
             Pure rbtree'
             (requires (pre_balance c lt ky rt))
             (ensures (fun r -> post_balance c lt ky rt r))

#reset-options "--z3rlimit 40"

(* it's pretty cool that the spec is proved easily without any hints ! *)
let balance c lt ky rt =
  match (c, lt, ky, rt) with
    | (B, (T R (T R a x b) y c), z, d)
    | (B, (T R a x (T R b y c)), z, d)
    | (B, a, x, (T R (T R b y c) z d))
    | (B, a, x, (T R b y (T R c z d))) -> T R (T B a x b) y (T B c z d)
    | _ -> T c lt ky rt

#reset-options "--z3rlimit 10"

(*
 * a helper function that inserts a red node with new key, and calls
 * balance to re-establish red black tree invariants
 *)
val ins: t:rbtree' -> k:nat ->
         Pure rbtree'
         (requires (c_inv t /\ h_inv t /\ k_inv t))
         (ensures (fun r ->

          (* returned tree is a T *)
          (T? r) /\

          (*
           * returned tree satisfies k_inv
           * moreover, min elt in returned tree is either k (the new key)
           * or same as the min elt in input t (resp. for max element)
           * if t is E, then min (and max) elt in returned tree must be k
           *)

          (k_inv r /\
          (min_elt r = k \/ (T? t /\ min_elt r = min_elt t)) /\
          (max_elt r = k \/ (T? t /\ max_elt r = max_elt t))) /\

          (*
           * returned tree satisfies h_inv
           * and has same black height as the input tree
           * (the new node is introduced at color R, and no node is re-colored)
           *)
          (h_inv r /\ black_height r = black_height t) /\

          (*
           * these are copied from post condition of balance
           *)
          (c_inv r \/
          (T? t /\ T?.col r = R /\ T?.col t = R /\ not_c_inv r /\ lr_c_inv r)) /\

          (*
           * returned tree has all the elements of t and k and nothing else
           *)
          (forall k'. (in_tree t k' ==> in_tree r k') /\
                      (in_tree r k' ==> (in_tree t k' \/ k' = k)))

          ))
(* once again, very cool that spec is verified without any hints in the code *)
let rec ins t x =
  match t with
    | E -> T R E x E
    | T c a y b ->
      if x < y then
        (* TODO: ideally we would have inlined this call in the balance call *)
        (* NS: You can write it this way. We're generating a semantically correct VC, but the shape of it causes Z3 to blowup *)
        (* balance c (ins a x) y b *)
        let lt = ins a x in
        balance c lt y b
      else if x = y then
        t
      else
        let rt = ins b x in
        balance c a y rt

(*
 * a red black tree is balanced if it satisfies r_inv, h_inv, c_inv, and k_inv
 *)
type balanced_rbtree' (t:rbtree') = r_inv t /\ h_inv t /\ c_inv t /\ k_inv t

(*
 * make black blackens the root of a tree
 *)
val make_black: t:rbtree' -> Pure rbtree'
                            (requires (T? t /\ c_inv t /\ h_inv t /\ k_inv t))
                            (ensures (fun r -> balanced_rbtree' r
                            /\ (forall k. in_tree t k <==> in_tree r k)))
let make_black (T _ a x b) = T B a x b

(*
 * and finally, the beautiful spec of insert function :)
 *)
val insert: t:rbtree' -> x:nat -> Pure rbtree'
                                  (requires (balanced_rbtree' t))
                                  (ensures (fun r -> balanced_rbtree' r /\
                                  (forall k'.
                                  (in_tree t k' ==> in_tree r k') /\
                                  (in_tree r k' ==> (in_tree t k' \/ k' = x))
                                  )))

let insert t x =
  let r = ins t x in
  let r' = make_black r in
  r'

(* TODO: make rbtree polymorphic *)

noeq type rbtree =
  | Mk: tr:rbtree'{balanced_rbtree' tr} -> rbtree

val proj: rbtree -> Pure rbtree' (requires True) (ensures (fun r -> balanced_rbtree' r))
let proj tr = Mk?.tr tr

(*TODO - move the above F* spec of RB tree to a new file after module loading issue is resolved*)
(* /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)

(* Pulse Implementation of RB tree*)
#lang-pulse

open Pulse.Lib.Pervasives

noeq type node = {
    col : color;
    left : tree_t;
    key : nat;
    right : tree_t;
}

and node_ptr = ref (node)
//A nullable pointer to a node
and tree_t  = option (node_ptr)


let rec is_tree  (ct:tree_t) (ft:rbtree')
    : Tot slprop (decreases ft) =
  match ft with
  | E -> pure (ct == None)
  | T  col left' key right' ->
            exists* (p:node_ptr) (lct:tree_t) (rct:tree_t).
            pure (ct == Some p) **
            pts_to p {col = col; left = lct; key = key;  right = rct} **
            is_tree lct left' **
            is_tree rct right'
  


ghost
fn elim_is_tree_E (x:tree_t)
  requires is_tree x E
  ensures pure (x == None)
{
   unfold (is_tree x E) 
}



ghost
fn intro_is_tree_E (x:tree_t) 
  requires pure (x == None)
  ensures is_tree x E
{
  fold (is_tree x E); 
}


ghost
fn elim_is_tree_node (ct:tree_t) (colr:color) (key:nat) (ltree:rbtree') (rtree:rbtree')
  requires is_tree ct (T colr ltree key rtree)
  ensures (
  exists* (p:node_ptr) (lct:tree_t) (rct:tree_t).
    pure (ct == Some p) **
    pts_to p {col=colr; left = lct; key = key; right = rct} **
    is_tree lct ltree **
    is_tree rct rtree
)
{
  unfold is_tree;
  ()
}

module G = FStar.Ghost


ghost
fn intro_is_tree_node (ct:tree_t) (v:node_ptr) (#node:node) (#ltree:rbtree') (#rtree:rbtree')
requires
  pts_to v node **
  is_tree node.left ltree **
  is_tree node.right rtree **
  pure (ct == Some v)
ensures
  is_tree ct (T node.col ltree node.key rtree)
{
   fold (is_tree ct (T node.col ltree node.key rtree))
}

let is_tree_cases (x : option (ref (node))) (ft : rbtree')
= match x with
  | None -> pure (ft == E)
  | Some v -> 
    exists* (n:node) (ltree:rbtree') (rtree:rbtree').
      pts_to v n **
      pure (ft == T n.col ltree n.key rtree) **
      is_tree n.left ltree **
      is_tree n.right rtree

ghost
fn cases_of_is_tree  (x:tree_t) (ft: rbtree')
  requires is_tree x ft
  ensures  is_tree_cases x ft
{
  match ft {
    E -> {
      unfold (is_tree x E);
      fold (is_tree_cases None ft);
    }
    T col ltree key rtree -> {
      unfold (is_tree x (T col ltree key rtree));
      with p lct rct. _;
      with n. assert pts_to p n;
      with l'. rewrite is_tree lct l' as is_tree n.left l';
      with r'. rewrite is_tree rct r' as is_tree n.right r';
      fold (is_tree_cases (Some p) (T col ltree key rtree))
    }
  }
}

ghost
fn is_tree_case_none (x:tree_t) (#l:rbtree')
  requires is_tree x l ** pure (x == None)
  ensures  is_tree x l ** pure (l == E)
{
  rewrite each x as None;
  cases_of_is_tree None l;
  unfold is_tree_cases;
  intro_is_tree_E x;
  ()
}

ghost
fn is_tree_case_some (x:tree_t) (v:node_ptr) (#ft:rbtree') 
  requires is_tree x ft ** pure (x == Some v)
ensures
   exists* (node:node) (ltree:rbtree') (rtree:rbtree').
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T node.col ltree node.key rtree)
  
{
  rewrite each x as Some v;
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
}

(* 
   F* Spec
   val color_of: t:rbtree' -> Tot color
   let color_of t = match t with
     | E -> B
  |   T c _ _ _ -> c *)

(* Pulse implementation *)
  
fn rec color_t (x:tree_t)
  requires is_tree x 'l
  returns c:color
  ensures is_tree x 'l ** pure (c == color_of 'l)
  {
    match x {
    None -> {
       is_tree_case_none None;
       rewrite is_tree None 'l as is_tree x 'l;
       B
    }
    Some vl -> {
       is_tree_case_some (Some vl) vl;
       with gnode. assert pts_to vl gnode;
       let node = !vl;
       rewrite each gnode as node;
       let colr = node.col;
       intro_is_tree_node x vl;
       colr
   }
 }
}

(*val black_height: t:rbtree' -> Tot (option nat)
let rec black_height t = match t with
  | E -> Some 0
  | T c a _ b ->
    (*
     * TODO: ideally we should be able to write match (black_height a, black_height b)
     *)
    let hha = black_height a in
    let hhb = black_height b in
    match (hha, hhb) with
      | Some ha, Some hb ->
        if ha = hb then
          if c = R then Some ha else Some (ha + 1)
        else
          None
      | _, _ -> None*)

let none_term ()
   : Tot (o:option nat{o == None}) = None

fn rec black_height_t (x:tree_t)
  requires is_tree x 'l
  returns h:(option nat)
  ensures is_tree x 'l ** pure (h == black_height 'l)
{
   match x {
    None -> {
       is_tree_case_none None;
       rewrite is_tree None 'l as is_tree x 'l;
       Some 0
    }
    Some vl -> {
       is_tree_case_some (Some vl) vl;
       with gnode. assert pts_to vl gnode;
       let node = !vl;
       rewrite each gnode as node;
       let l_height = black_height_t node.left;
       let r_height = black_height_t node.right;
       intro_is_tree_node x vl;
       match l_height {
         Some ha -> {
           match r_height {
            Some hb -> {
              let b:bool = ha = hb;
              if b {
                let b1:bool = node.col = R;
                if b1 {
                  Some ha
                }
                else
                {
                  Some (ha + 1)
                }
              }
              else
              {
                none_term ();
              }
            }
            None -> {
              none_term ();
            }
           }
         }
        None -> {
          match r_height {
            Some hb -> {
              none_term ();
            }
            None -> {
              
              None #nat; //Either use none_term () or None #nat
            }
           }
        }
       }
   }
 }
}

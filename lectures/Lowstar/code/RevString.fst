module RevString

open FStar.List.Tot
open FStar.Seq

let rec rev_list l =
  match l with
  | [] -> []
  | h::t -> rev_list t @ [h]

val swap : #a:eqtype -> s:seq a -> i:nat{i < Seq.length s} -> j:nat{j < Seq.length s} -> seq a
let swap s i j =
  let ei = Seq.index s i in
  let ej = Seq.index s j in
  let s' = Seq.upd s i ej in
  Seq.upd s' j ei

val rev_seq' : #a:eqtype -> s:seq a -> i:nat{i <= Seq.length s} -> Tot (seq a) (decreases (Seq.length s - i))
let rec rev_seq' s i =
  if i < Seq.length s / 2 then
    let s' = swap s i (Seq.length s - i - 1) in
    rev_seq' s' (i + 1)
  else
    s

let rev_seq s = rev_seq' s 0
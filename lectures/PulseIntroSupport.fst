module PulseIntroSupport

open FStar.All
open FStar.Ref

val incr : r:ref int -> FStar.All.St unit
let incr r =
  (r := (!r + 1))

val incr2 : r:ref int -> ST unit (requires (fun h0 -> True))
  (ensures (fun h0 _ h2 ->
    modifies !{r} h0 h2 /\
    sel h2 r == sel h0 r + 1))
let incr2 r = r := !r + 1

val incr3 : x:ref int -> y:ref int -> ST unit
  (requires (fun h0 -> addr_of x <> addr_of y)) (* Non-aliasing is necessary *)
  (ensures (fun h0 _ h2 ->
    modifies !{x} h0 h2 /\
    sel h2 x == sel h0 x + 1 /\
    sel h2 y == sel h0 y))
let incr3 x y = x := !x + 1


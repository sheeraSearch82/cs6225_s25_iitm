module Math

open FStar.HyperStack.ST

let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x

let abs (x: Int32.t): Pure Int32.t
  (requires Int32.v x <> Int.min_int 32)
  (ensures fun r -> Int32.v r >= 0)
=
  let open FStar.Int32 in
  if x >=^ 0l then
    x
  else
    0l -^ x

let abs2 (x: Int32.t): option Int32.t =
  let open FStar.Int32 in
  if Int32.v x = Int.min_int 32 then
    None
  else if x >=^ 0l then
    Some x
  else
    Some (0l -^ x)

(* Algebraic data types are compiled to tagged enums

typedef enum { FStar_Pervasives_Native_None, FStar_Pervasives_Native_Some }
FStar_Pervasives_Native_option__int32_t_tags;

typedef struct FStar_Pervasives_Native_option__int32_t_s
{
  FStar_Pervasives_Native_option__int32_t_tags tag;
  int32_t v;
}
FStar_Pervasives_Native_option__int32_t;
*)

let main () : St Int32.t = 0l
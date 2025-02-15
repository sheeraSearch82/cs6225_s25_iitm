#require "fstar.lib";;
#use "Fstar_quicksort.ml";;

let l = [3;2;1];;
let sorted_l = sort (List.map Prims.of_int l);;
List.map Prims.to_string sorted_l;;

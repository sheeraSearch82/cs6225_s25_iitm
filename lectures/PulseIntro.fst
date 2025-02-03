module PulseIntro
#lang-pulse
open Pulse

let fstar_five : int = 5

fn five ()
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  fstar_five
}

let pulse_five_in_fstar = five ()

let pulse_five : int = 5
import Std.WP
import Std.Tactic.Do
open Std.WP Lean.Order

def sum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem sum_correct (l : Array Nat) : sum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : sum l = x
  apply Id.of_run_eq_wp h
  -- Break down into verification conditions
  vcgen
  -- Specify the invariant which should hold throughout the loop.
  -- It is a function of three arguments:
  -- * `pref` is the list of elements that the loop has already visited
  -- * `suff` is the list of elements that the loop has yet to visit
  -- * `out` is the current value of the `let mut` variable
  -- Our invariant is that `out` holds the sum of the prefix.
  case inv1 => exact fun pref suff out => pref.sum = out
  -- Prove that the invariant is true at the start
  case vc1 => trivial
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc2 finalOut hInv => simp [hInv.symm]
  -- Prove that our invariant is preserved at each step of the loop
  case vc3 pref curr suff hsplit oldOut hInv => simp[out, hInv]



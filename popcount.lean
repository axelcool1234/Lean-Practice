import Std.WP
import Std.Tactic.Do

open scoped Std.WP

def popcount (x : BitVec 64) : BitVec 64 := Id.run do
  let mut x := x
  let mut count : BitVec 64 := 0
  while x != 0 do
    x := x &&& (x - 1)
    count := count + 1
  return count


def popcount_correct : ∀ x : BitVec 64, popcount x = x.cpop := by
  intro x
  unfold popcount
  apply Std.WP.Id.of_run_eq_wp rfl (fun result => result = x.cpop)
  vcgen invariants

  sorry

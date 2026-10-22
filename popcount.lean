import Std.WP
import Std.Tactic.Do

import Std.Tactic.BVDecide
import Init.Internal.Order.While

open scoped Std.WP

def popcount' (x : BitVec 64) : BitVec 64 := Id.run do
  let mut x := x
  let mut count : BitVec 64 := 0
  while x != 0 do
    x := x &&& (x - 1)
    count := count + 1
  return count

theorem Nat.one_le_nonzero (x : Nat) (h : x ≠ 0) : 1 ≤ x := by
  obtain ⟨y : Nat, h' : x = y.succ⟩ := by 
    apply Nat.exists_eq_succ_of_ne_zero
    assumption
  rw [h']
  apply Nat.succ_le_succ 
  apply Nat.zero_le

def popcount (x : BitVec 64) : BitVec 64 :=
  if h : x = 0 then
    0
  else
    popcount (x &&& (x - 1)) + 1
termination_by x.toNat
decreasing_by
  apply Nat.lt_of_le_of_lt (m := (x - 1).toNat)
  · rw [BitVec.toNat_and]
    apply Nat.and_le_right
  · rw [BitVec.toNat_sub_of_le]
    · apply Nat.sub_one_lt
      intro hneq
      apply h
      apply BitVec.eq_of_toNat_eq
      apply hneq
    · apply Nat.one_le_nonzero 
      intro hneq
      apply h
      apply BitVec.eq_of_toNat_eq
      assumption

theorem popcount_correct : ∀ x : BitVec 64, popcount x = x.cpop := by
  intro x
  induction x using popcount.induct with
  | case1 => simp [popcount]
  | case2 x h ih => 
    unfold popcount
    split
    · contradiction
    · rw [ih]
      clear ih
      bv_decide


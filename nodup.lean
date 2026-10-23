import Std.WP
import Std.Tactic.Do
import Std.Data.HashSet
import Mathlib.Data.List.Nodup
open Std.WP Lean.Order

-- A future 4.36 release adds these annotations to the library.
attribute [local grind norm]
  Lean.Order.ofProp_prop_eq Lean.Order.meet_prop_eq_and
  Lean.Order.join_prop_eq_or Lean.Order.iSup_prop_eq_exists

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_run_eq_wp h
  vcgen
  case inv1 =>
    exact Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ret = false ∧ ¬l.Nodup)
      (onContinue := fun pref suff seen =>
        (∀ x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup) 
  -- Establish the invariant in the initial state
  case vc1 => simp [seen]
  -- Early return postcondition: returning false corresponds to `¬l.Nodup`
  case vc2 returnValue? finalSeen hInv ret hReturned => 
    simp [Invariant.withEarlyReturnNewDo, hReturned] at hInv
    obtain ⟨hRetFalse, hNotNodup⟩ := hInv
    constructor
    · intro hRetTrue
      subst ret
      contradiction
    · intro hNodup
      contradiction
  -- Normal completion postcondition: returning true corresponds to `l.Nodup`
  case vc3 returnValue? finalSeen hInv hContinued =>
    simp [Invariant.withEarlyReturnNewDo, hContinued] at hInv
    obtain ⟨hInPref, hNodup⟩ := hInv
    constructor
    · intro
      assumption
    · intro
      trivial
  -- Duplicate branch: `curr` was already seen, so return false and establish `¬l.Nodup`
  case vc4 pref curr suff hsplit returnValue? currentSeen hInv hMem => 
    simp [Invariant.withEarlyReturnNewDo] at *
    obtain ⟨_, hSeenIffInPref, _⟩ := hInv
    specialize hSeenIffInPref curr
    have hInPref : curr ∈ pref := hSeenIffInPref.mp hMem
    intro hNodup
    subst hsplit
    simp [List.nodup_append'] at hNodup
    obtain ⟨_, _, hNotInPref, _⟩ := hNodup
    contradiction
  -- Fresh branch: insert `curr` and preserve the continuation invariant
  case vc5 pref curr suff hsplit returnValue? currentSeen hInv hNotMem => 
    simp [Invariant.withEarlyReturnNewDo] at *
    obtain ⟨_, hSeenIffInPref, _⟩ := hInv
    constructor
    · intro x
      specialize hSeenIffInPref x
      constructor
      · intro hInSeen
        subst seen

      · sorry
    · sorry


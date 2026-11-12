import Std

/-!
# Insertion sort: a proof worksheet

Based on the exercise sequence in Software Foundations, Volume 3:
https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html

Work through the five exercises in Part 2 first. Replace each `sorry` with
your proof; the later sections are extra challenges. The comments give
small hints, so you can skip them if you prefer to work unaided.

This file uses ordinary Lean declarations and needs only the standard library.
Everything lives in `InsertionSort`, so names stay local to this worksheet.

Lean notation guide:
* `List.Perm l₁ l₂` corresponds to the book's `Permutation l₁ l₂`.
* `l[i]?` corresponds to `nth_error l i`; it returns an `Option Nat`.
* `l[i]?.getD 0` corresponds to `nth i l 0`.
* `by_cases h : a ≤ b` replaces the book's Boolean comparison case split.
  Then `simp [insert, h]` reduces the relevant branch of `insert`.
* `omega` can discharge arithmetic goals about natural numbers.
-/

namespace InsertionSort

/-! ## Part 1: The program and its contract -/

/-- Insert an element at its ordered position, assuming the input is sorted. -/
def insert (i : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [i]
  | h :: t => if i ≤ h then i :: h :: t else h :: insert i t

def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)

example : sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] =
    [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  rfl

example : insert 7 [1, 3, 4, 8, 12, 14, 18] =
    [1, 3, 4, 7, 8, 12, 14, 18] := by
  rfl

/-- An inductive account of sortedness, called `sorted` in the book. -/
inductive Sorted : List Nat → Prop where
  | nil : Sorted []
  | single (a : Nat) : Sorted [a]
  | cons (a b : Nat) (l : List Nat)
      (hab : a ≤ b) (h : Sorted (b :: l)) : Sorted (a :: b :: l)

/-- An index-based account, called `sorted'` in the book. -/
def Sorted' (l : List Nat) : Prop :=
  ∀ (i j a b : Nat), i < j → l[i]? = some a → l[j]? = some b → a ≤ b

/-- An account with explicit bounds, called `sorted''` in the book. -/
def Sorted'' (l : List Nat) : Prop :=
  ∀ (i j : Nat), i < j → j < l.length → l[i]?.getD 0 ≤ l[j]?.getD 0

/-- Correct sorting preserves every occurrence and produces ordered output. -/
def IsSortingAlgorithm (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Perm l (f l) ∧ Sorted (f l)

/-! ## Part 2: Prove insertion sort correct -/

/-
Exercise 1 (3 stars): insert_sorted

Try induction on the evidence `h`, rather than on `l`.
The constructors available for the resulting goals are `Sorted.nil`,
`Sorted.single`, and `Sorted.cons`. Case analysis on a sortedness proof
can also tell you about the head elements of its list.
-/
theorem insert_sorted (a : Nat) (l : List Nat) (h : Sorted l) :
    Sorted (insert a l) := by
  sorry

/-
Exercise 2 (2 stars): sort_sorted

Use list induction and Exercise 1.
-/
theorem sort_sorted (l : List Nat) : Sorted (sort l) := by
  sorry

/-
Exercise 3 (3 stars): insert_perm

Useful library facts (hover over the names for their types):
  List.Perm.refl   List.Perm.cons   List.Perm.swap   List.Perm.trans

Note the direction of `List.Perm.swap a b l`:
it relates `b :: a :: l` to `a :: b :: l`.
-/
theorem insert_perm (a : Nat) (l : List Nat) :
    List.Perm (a :: l) (insert a l) := by
  sorry

/-
Exercise 4 (3 stars): sort_perm

Combine the induction hypothesis with Exercise 3 using transitivity.
-/
theorem sort_perm (l : List Nat) : List.Perm l (sort l) := by
  sorry

/-
Exercise 5 (1 star): insertion_sort_correct

Assemble the two properties in the contract.
-/
theorem insertion_sort_correct : IsSortingAlgorithm sort := by
  sorry

/-! ## Part 3: Compare specifications (advanced) -/

/-
Exercise 6 (4 stars): sorted_sorted'

Induct on `h`. Keep the indices and their values generalized so that
the induction hypothesis can be used at smaller indices.
Splitting natural numbers into zero and successor cases is useful here.
-/
theorem sorted_sorted' (l : List Nat) (h : Sorted l) : Sorted' l := by
  sorry

/-
Exercise 7 (3 stars): sorted'_sorted

Try list induction. Derive a statement about the tail by shifting both
indices by one. To compare adjacent heads, specialize the hypothesis
at indices 0 and 1.
-/
theorem sorted'_sorted (l : List Nat) (h : Sorted' l) : Sorted l := by
  sorry

/-! ## Part 4: Prove the index-based specification directly (optional) -/

/-
For this section, work directly with `Sorted'`. Avoid using
`sorted_sorted'`, `sorted'_sorted`, `insert_sorted`, and `sort_sorted`.
You may introduce additional helper lemmas.

Exercise 8a: nth_error_insert

An entry in the result is either the inserted value or an entry from the
input. The name follows the book; indexing here uses Lean's `l[i]?`.
-/
theorem nth_error_insert (l : List Nat) (a i v : Nat)
    (h : (insert a l)[i]? = some v) :
    a = v ∨ ∃ (j : Nat), l[j]? = some v := by
  sorry

/-
Exercise 8b (5 stars, together with 8a): insert_sorted'

The previous helper describes where result values come from. You may
also need to reason about how their positions change during insertion.
-/
theorem insert_sorted' (a : Nat) (l : List Nat) (h : Sorted' l) :
    Sorted' (insert a l) := by
  sorry

/-- Once insertion preserves the index-based contract, sorting follows. -/
theorem sort_sorted' (l : List Nat) : Sorted' (sort l) := by
  induction l with
  | nil =>
      intro i j a b hij hi hj
      simp [sort] at hi
  | cons a l ih =>
      exact insert_sorted' a (sort l) ih

end InsertionSort

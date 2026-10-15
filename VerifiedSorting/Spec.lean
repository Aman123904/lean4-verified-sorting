/-!
# What it means to sort

A function `f : List Nat → List Nat` is a correct sort when its output is
ordered and is a permutation of its input.
-/

namespace VerifiedSorting

/-- A list is sorted when every element is `≤` every later element. -/
abbrev Sorted (l : List Nat) : Prop := l.Pairwise (· ≤ ·)

/-- The specification every sorting function must meet. -/
structure IsSort (f : List Nat → List Nat) : Prop where
  sorted : ∀ l, Sorted (f l)
  perm   : ∀ l, (f l).Perm l

end VerifiedSorting

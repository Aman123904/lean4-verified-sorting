import VerifiedSorting.Spec

/-!
# Insertion sort, verified
-/

namespace VerifiedSorting

/-- Insert `x` into a sorted list, keeping it sorted. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

theorem insert_perm (x : Nat) (l : List Nat) : (insert x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold insert
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem mem_insert {x z : Nat} {l : List Nat} : z ∈ insert x l ↔ z = x ∨ z ∈ l := by
  simpa using (insert_perm x l).mem_iff

theorem insert_sorted (x : Nat) {l : List Nat} (h : Sorted l) : Sorted (insert x l) := by
  induction l with
  | nil => simp [insert]
  | cons y ys ih =>
    replace h := List.pairwise_cons.mp h
    unfold insert
    split
    · rename_i hxy
      refine List.Pairwise.cons ?_ (List.Pairwise.cons h.1 h.2)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (h.1 z hz)
    · rename_i hxy
      refine List.Pairwise.cons ?_ (ih h.2)
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · omega
      · exact h.1 z hz

theorem insertionSort_sorted (l : List Nat) : Sorted (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort]
  | cons x xs ih => exact insert_sorted x ih

theorem insertionSort_perm (l : List Nat) : (insertionSort l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insert_perm x _).trans (ih.cons x)

/-- **Insertion sort is a correct sorting algorithm.** -/
theorem insertionSort_isSort : IsSort insertionSort :=
  ⟨insertionSort_sorted, insertionSort_perm⟩

example : insertionSort [5, 2, 9, 1, 5, 6] = [1, 2, 5, 5, 6, 9] := by decide

end VerifiedSorting

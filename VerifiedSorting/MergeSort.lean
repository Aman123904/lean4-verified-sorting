import VerifiedSorting.Spec

/-!
# Merge sort, verified

Termination of `merge` and `mergeSort` is proved by well-founded recursion
on list length.
-/

namespace VerifiedSorting

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/-- Split a list into the elements at even and at odd positions. -/
def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    (x :: (split rest).1, y :: (split rest).2)

theorem split_length (l : List Nat) :
    (split l).1.length + (split l).2.length = l.length ∧
    (split l).1.length ≤ (l.length + 1) / 2 ∧ (split l).2.length ≤ l.length / 2 := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 => simp [split]
  | case3 x y rest ih => simp only [split, List.length_cons]; omega

def mergeSort (l : List Nat) : List Nat :=
  if h : l.length < 2 then l
  else
    have h1 : (split l).1.length < l.length := by have := split_length l; omega
    have h2 : (split l).2.length < l.length := by have := split_length l; omega
    merge (mergeSort (split l).1) (mergeSort (split l).2)
termination_by l.length

theorem merge_perm (xs ys : List Nat) : (merge xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simp [merge]
  | case2 xs h => cases xs <;> simp_all [merge]
  | case3 x xs y ys hxy ih =>
    simp only [merge, hxy, ↓reduceIte, List.cons_append]
    exact ih.cons x
  | case4 x xs y ys hxy ih =>
    simp only [merge, hxy, ↓reduceIte]
    exact (ih.cons y).trans List.perm_middle.symm

theorem merge_sorted {xs ys : List Nat} (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (merge xs ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simpa [merge] using hy
  | case2 xs h => cases xs <;> simp_all [merge]
  | case3 x xs y ys hxy ih =>
    simp only [merge, hxy, ↓reduceIte]
    replace hx := List.pairwise_cons.mp hx
    refine List.Pairwise.cons ?_ (ih hx.2 hy)
    intro z hz
    rcases List.mem_append.mp ((merge_perm _ _).mem_iff.mp hz) with hz | hz
    · exact hx.1 z hz
    · replace hy := List.pairwise_cons.mp hy
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (hy.1 z hz)
  | case4 x xs y ys hxy ih =>
    simp only [merge, hxy, ↓reduceIte]
    replace hy := List.pairwise_cons.mp hy
    refine List.Pairwise.cons ?_ (ih hx hy.2)
    intro z hz
    rcases List.mem_append.mp ((merge_perm _ _).mem_iff.mp hz) with hz | hz
    · replace hx := List.pairwise_cons.mp hx
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact Nat.le_trans (by omega) (hx.1 z hz)
    · exact hy.1 z hz

theorem split_perm (l : List Nat) : ((split l).1 ++ (split l).2).Perm l := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 => simp [split]
  | case3 x y rest ih =>
    simp only [split, List.cons_append]
    exact (List.perm_middle.trans (ih.cons y)).cons x

theorem mergeSort_sorted_perm (l : List Nat) :
    Sorted (mergeSort l) ∧ (mergeSort l).Perm l := by
  induction l using mergeSort.induct with
  | case1 l h =>
    rw [mergeSort]; simp only [h, ↓reduceDIte]
    refine ⟨?_, List.Perm.refl _⟩
    match l, h with
    | [], _ => simp
    | [_], _ => simp
  | case2 l h _ _ ih1 ih2 =>
    rw [mergeSort]; simp only [h, ↓reduceDIte]
    exact ⟨merge_sorted ih1.1 ih2.1,
      (merge_perm _ _).trans ((ih1.2.append ih2.2).trans (split_perm l))⟩

/-- **Merge sort is a correct sorting algorithm.** -/
theorem mergeSort_isSort : IsSort mergeSort :=
  ⟨fun l => (mergeSort_sorted_perm l).1, fun l => (mergeSort_sorted_perm l).2⟩

#guard mergeSort [5, 2, 9, 1, 5, 6] == [1, 2, 5, 5, 6, 9]

end VerifiedSorting

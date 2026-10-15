import VerifiedSorting.InsertionSort
import VerifiedSorting.MergeSort

/-!
# Sorting is unique

Any two lists that are sorted permutations of each other are equal. Hence
*every* function meeting `IsSort` computes the same thing, and in particular
merge sort and insertion sort agree on all inputs.
-/

namespace VerifiedSorting

theorem sorted_perm_eq : ∀ {l₁ l₂ : List Nat},
    Sorted l₁ → Sorted l₂ → l₁.Perm l₂ → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hp => absurd hp.length_eq (by simp)
  | _ :: _, [], _, _, hp => absurd hp.length_eq (by simp)
  | a :: as, b :: bs, h₁, h₂, hp => by
    replace h₁ := List.pairwise_cons.mp h₁
    replace h₂ := List.pairwise_cons.mp h₂
    have hab : a = b := by
      have ha : a ∈ b :: bs := hp.mem_iff.mp (List.mem_cons_self ..)
      have hb : b ∈ a :: as := hp.mem_iff.mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      have := h₁.1 b hb; have := h₂.1 a ha; omega
    subst hab
    rw [sorted_perm_eq h₁.2 h₂.2 ((List.perm_cons a).mp hp)]

/-- Two correct sorting functions agree everywhere. -/
theorem IsSort.unique {f g : List Nat → List Nat} (hf : IsSort f) (hg : IsSort g) :
    ∀ l, f l = g l := fun l =>
  sorted_perm_eq (hf.sorted l) (hg.sorted l) ((hf.perm l).trans (hg.perm l).symm)

theorem mergeSort_eq_insertionSort (l : List Nat) : mergeSort l = insertionSort l :=
  mergeSort_isSort.unique insertionSort_isSort l

end VerifiedSorting

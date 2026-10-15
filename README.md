# Verified Sorting in Lean 4

[![Lean CI](https://github.com/Aman123904/lean4-verified-sorting/actions/workflows/ci.yml/badge.svg)](https://github.com/Aman123904/lean4-verified-sorting/actions/workflows/ci.yml)

**Insertion sort** and **merge sort**, each proved correct in Lean 4: the output is sorted and is a permutation of the input. A uniqueness theorem then shows that any two correct sorting functions agree, so the two algorithms compute the same function. It uses no Mathlib and has no `sorry`.

## Main theorems

| Theorem | Statement |
|---|---|
| `insertionSort_isSort` | Insertion sort meets the sorting spec. |
| `mergeSort_isSort` | Merge sort (well-founded recursion) meets the sorting spec. |
| `sorted_perm_eq` | Two sorted lists that are permutations of each other are equal. |
| `IsSort.unique` | All correct sorting functions are extensionally equal. |
| `mergeSort_eq_insertionSort` | `mergeSort l = insertionSort l` for every `l`. |

## Layout

- `VerifiedSorting/Spec.lean`: what "a correct sort" means (`IsSort`)
- `VerifiedSorting/InsertionSort.lean`
- `VerifiedSorting/MergeSort.lean`: termination by list length, proofs by functional induction
- `VerifiedSorting/Uniqueness.lean`

## Build

```bash
lake build
```

Toolchain: `leanprover/lean4:v4.34.1`.

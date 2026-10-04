import PlanarHom.ExponentVectors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.FinRange

/-! Frequency vectors of actual selected-entry words, with exact product identities. -/

open scoped BigOperators
namespace PlanarHom.WordFrequencies
variable {t : ℕ}

/-- Canonical frequency vector in the fixed alphabet order. -/
def frequencies (xs : List (Fin t)) : List ℕ := List.ofFn (fun i : Fin t => xs.count i)

@[simp] theorem frequencies_length (xs : List (Fin t)) : (frequencies xs).length = t := by
  simp [frequencies]

theorem sum_counts (xs : List (Fin t)) : (∑ i : Fin t, xs.count i) = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
    have h : (∑ i : Fin t, if a == i then 1 else 0) = 1 := by simp
    rw [h, ih]

@[simp] theorem frequencies_sum (xs : List (Fin t)) : (frequencies xs).sum = xs.length := by
  simpa only [frequencies, List.sum_ofFn] using sum_counts xs

theorem frequencies_mem_weak (xs : List (Fin t)) :
    frequencies xs ∈ ExponentVectors.weak t xs.length := by
  exact (ExponentVectors.mem_weak _ _ _).mpr ⟨frequencies_length xs, frequencies_sum xs⟩

/-- Reordering an actual word by its frequency vector preserves its field product. -/
theorem product_eq_frequencies {K : Type} [CommMonoid K] (A : Fin t → K) (xs : List (Fin t)) :
    (xs.map A).prod = ∏ i : Fin t, A i ^ xs.count i := by
  classical
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.count_eq_zero_of_not_mem (by simpa using hi), pow_zero]

end PlanarHom.WordFrequencies

import PlanarHom.WordFrequencies
import PlanarHom.ProductCompatibility
import Mathlib.Data.List.GetD

/-! Concrete exponent products, expanded words, and target consistency on numerical collisions. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.ExponentProductSemantics
open ProductCompatibility
variable {t : ℕ} {K : Type} [Field K]

/-- The fixed-coordinate field product of one explicitly encoded exponent list. -/
def value (A : Fin t → K) (xs : List ℕ) : K := ∏ i : Fin t, A i ^ xs.getD i.val 0

/-- Expand only for the correctness/height proof; no exponential-time expansion is used by the machine. -/
def expand (t : ℕ) (xs : List ℕ) : List (Fin t) :=
  (List.ofFn (fun i : Fin t => List.replicate (xs.getD i.val 0) i)).flatten

theorem expand_length (xs : List ℕ) (hlen : xs.length = t) : (expand t xs).length = xs.sum := by
  subst t
  simp only [expand, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_replicate]
  have h : (List.ofFn (fun i : Fin xs.length => xs.getD i.val 0)) = xs := by
    simpa only [List.getD_eq_getElem _ _ (Fin.isLt _)] using List.ofFn_getElem xs
  rw [h]

theorem expand_product (A : Fin t → K) (xs : List ℕ) :
    ((expand t xs).map A).prod = value A xs := by
  simp [expand, value, List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn,
    List.map_replicate, Function.comp_def]

theorem value_frequencies (A : Fin t → K) (word : List (Fin t)) :
    value A (WordFrequencies.frequencies word) = (word.map A).prod := by
  rw [WordFrequencies.product_eq_frequencies]
  apply Finset.prod_congr rfl
  intro i _
  simp [value, WordFrequencies.frequencies, List.getD_eq_getElem]

/-- Equal nonzero source products of enumerated vectors have the same target value.
No evaluation oracle for the source's abstract θ map is needed. -/
theorem target_eq_of_weak_collision (A B : Fin t → K) (h : Compatible A B)
    {m : ℕ} (xs ys : List ℕ) (hx : xs ∈ ExponentVectors.weak t m)
    (hy : ys ∈ ExponentVectors.weak t m) (hnz : value A xs ≠ 0)
    (heq : value A xs = value A ys) : value B xs = value B ys := by
  obtain ⟨hxl, hxs⟩ := (ExponentVectors.mem_weak t m xs).mp hx
  obtain ⟨hyl, hys⟩ := (ExponentVectors.mem_weak t m ys).mp hy
  have hlen : (expand t xs).length = (expand t ys).length := by
    rw [expand_length xs hxl, expand_length ys hyl, hxs, hys]
  simpa only [expand_product] using target_eq_of_nonzero_collision A B h
    (expand t xs) (expand t ys) hlen (by simpa only [expand_product] using hnz)
    (by simpa only [expand_product] using heq)

end PlanarHom.ExponentProductSemantics

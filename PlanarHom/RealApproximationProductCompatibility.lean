import PlanarHom.RelationApproximation
import PlanarHom.ProductCompatibility
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! NEW reconstruction: the numerical approximation implies the exact
finite-word collision hypothesis used by the represented interpolation machine.
Zeros are retained, and equality of entries is preserved automatically. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RelationApproximation
variable {I : Type} [Fintype I]

theorem list_product_eq_count {K : Type} [CommMonoid K] (xs : List I) (f : I → K) :
    (xs.map f).prod = ∏i, f i ^ xs.count i := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i hi hn
  have hni : i ∉ xs := by simpa using hn
  simp [List.count_eq_zero_of_not_mem hni]

theorem compatible_of_integer_relations (m : I → ℝ) (r : I → ℚ)
    (hm : ∀i, m i ≠ 0) (hr : ∀i, r i ≠ 0)
    (hrel : ∀z : I → ℤ, (∏i,m i ^ z i) = 1 → (∏i,r i ^ z i) = 1) :
    ProductCompatibility.Compatible m (fun i => (r i : ℝ)) := by
  intro xs ys hlen hxs hys heq
  have hh := prod_eq_of_preserves_integer_relations m r hm hr hrel
    (fun i => (xs.count i : ℤ)) (fun i => (ys.count i : ℤ))
    (by simpa only [zpow_natCast, ←list_product_eq_count] using heq)
  have hh' : (xs.map r).prod = (ys.map r).prod := by
    simpa only [zpow_natCast, ←list_product_eq_count] using hh
  simpa only [Rat.cast_list_prod, List.map_map, Function.comp_def] using
    congrArg (fun x : ℚ => (x : ℝ)) hh'

/-- Exact support, sign and collision preservation for a finite tuple with
arbitrary zero positions. The rational constants are chosen once, not computed
from a variable real input. -/
theorem rational_approximation_with_zeros (m : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃r : I → ℚ,
      (∀i, r i = 0 ↔ m i = 0) ∧
      (∀i, |(r i : ℝ) - m i| < δ) ∧
      (∀i, Real.sign (r i : ℝ) = Real.sign (m i)) ∧
      ProductCompatibility.Compatible m (fun i => (r i : ℝ)) := by
  let nz : I → ℝ := fun i => if m i = 0 then 1 else m i
  have hnz : ∀i, nz i ≠ 0 := by intro i; simp [nz]; split <;> simp_all
  obtain ⟨r,hr,ha,hs,hrel⟩ := relation_preserving_approximation nz hnz δ hδ
  let s : I → ℚ := fun i => if m i = 0 then 0 else r i
  have hc := compatible_of_integer_relations nz r hnz hr hrel
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : m i = 0 <;> simp [s,h,hr i]
  · intro i
    by_cases h : m i = 0
    · simpa [s,h] using hδ
    · simpa [s,nz,h] using ha i
  · intro i
    by_cases h : m i = 0
    · simp [s,h]
    · simpa [s,nz,h] using hs i
  · intro xs ys hl hx hy he
    have hxm : xs.map nz = xs.map m := List.map_congr_left (fun i hi => by simp [nz,hx i hi])
    have hym : ys.map nz = ys.map m := List.map_congr_left (fun i hi => by simp [nz,hy i hi])
    have hxs : xs.map (fun i => (s i : ℝ)) = xs.map (fun i => (r i : ℝ)) :=
      List.map_congr_left (fun i hi => by simp [s,hx i hi])
    have hys : ys.map (fun i => (s i : ℝ)) = ys.map (fun i => (r i : ℝ)) :=
      List.map_congr_left (fun i hi => by simp [s,hy i hi])
    rw [hxs,hys]
    exact hc xs ys hl (fun i _ => hnz i) (fun i _ => hnz i) (by rwa [hxm,hym])

theorem equal_entries_of_compatible {m s : I → ℝ}
    (hz : ∀i, m i = 0 → s i = 0) (hc : ProductCompatibility.Compatible m s)
    {i j : I} (h : m i = m j) : s i = s j := by
  by_cases hi : m i = 0
  · rw [hz i hi,hz j (h ▸ hi)]
  · have hj : m j ≠ 0 := h ▸ hi
    simpa using hc [i] [j] rfl (by simpa using hi) (by simpa using hj) (by simpa using h)

end PlanarHom.RelationApproximation

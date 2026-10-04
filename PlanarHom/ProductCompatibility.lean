import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Choose

/-! The exact equal-length-product hypothesis of source Lemma 3.1, without a computable θ. -/

noncomputable section
namespace PlanarHom.ProductCompatibility
variable {I K : Type} [Field K]

/-- Source Λ_m: products of m positions whose source entries are nonzero. -/
def ProductSet (A : I → K) (m : ℕ) : Set K :=
  {x | ∃ xs : List I, xs.length = m ∧ (∀ i ∈ xs, A i ≠ 0) ∧ (xs.map A).prod = x}

/-- Source condition (ii), with fixed-length lists representing tuples. The map
is mathematical data only; the reduction never evaluates it as an oracle. -/
def HasProductMaps (A B : I → K) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ θ : ProductSet A m → K,
    ∀ (xs : List I) (hlen : xs.length = m) (hnz : ∀ i ∈ xs, A i ≠ 0),
      θ ⟨(xs.map A).prod, ⟨xs, hlen, hnz, rfl⟩⟩ = (xs.map B).prod

/-- Equivalent collision invariant used by exact representative merging. -/
def Compatible (A B : I → K) : Prop :=
  ∀ xs ys : List I, xs.length = ys.length →
    (∀ i ∈ xs, A i ≠ 0) → (∀ i ∈ ys, A i ≠ 0) →
    (xs.map A).prod = (ys.map A).prod → (xs.map B).prod = (ys.map B).prod

/-- The source's maps imply collision consistency, including the separately trivial empty word. -/
theorem compatible_of_hasProductMaps (A B : I → K) (h : HasProductMaps A B) : Compatible A B := by
  intro xs ys hlen hxs hys heq
  by_cases hz : xs.length = 0
  · have hx : xs = [] := List.length_eq_zero_iff.mp hz
    have hy : ys = [] := List.length_eq_zero_iff.mp (hlen.symm.trans hz)
    simp [hx, hy]
  · obtain ⟨θ, hθ⟩ := h xs.length (Nat.pos_of_ne_zero hz)
    have hi : (⟨(xs.map A).prod, ⟨xs, rfl, hxs, rfl⟩⟩ : ProductSet A xs.length) =
        ⟨(ys.map A).prod, ⟨ys, hlen.symm, hys, rfl⟩⟩ := Subtype.ext heq
    rw [← hθ xs rfl hxs, ← hθ ys hlen.symm hys, hi]

/-- Conversely every well-defined product class admits the maps in the paper's hypothesis. -/
theorem hasProductMaps_of_compatible (A B : I → K) (h : Compatible A B) : HasProductMaps A B := by
  intro m _
  have hc : ∀ x : ProductSet A m, ∃ xs : List I,
      xs.length = m ∧ (∀ i ∈ xs, A i ≠ 0) ∧ (xs.map A).prod = x.val := fun x => x.property
  choose word hword using hc
  refine ⟨fun x => ((word x).map B).prod, ?_⟩
  intro xs hlen hnz
  let x : ProductSet A m := ⟨(xs.map A).prod, ⟨xs, hlen, hnz, rfl⟩⟩
  exact h (word x) xs ((hword x).1.trans hlen.symm) (hword x).2.1 hnz (hword x).2.2

theorem hasProductMaps_iff_compatible (A B : I → K) : HasProductMaps A B ↔ Compatible A B :=
  ⟨compatible_of_hasProductMaps A B, hasProductMaps_of_compatible A B⟩

/-- Nonzero source products provide exactly the source-position nonzeroness premise. -/
theorem all_nonzero_of_product_ne_zero (A : I → K) (xs : List I)
    (h : (xs.map A).prod ≠ 0) : ∀ i ∈ xs, A i ≠ 0 := by
  intro i hi hz
  apply h
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨i, hi, hz⟩

/-- Numerical collision merging uses target products of retained representatives,
not a hypothetical computable map θ. -/
theorem target_eq_of_nonzero_collision (A B : I → K) (h : Compatible A B)
    (xs ys : List I) (hlen : xs.length = ys.length)
    (hnz : (xs.map A).prod ≠ 0) (heq : (xs.map A).prod = (ys.map A).prod) :
    (xs.map B).prod = (ys.map B).prod :=
  h xs ys hlen (all_nonzero_of_product_ne_zero A xs hnz)
    (all_nonzero_of_product_ne_zero A ys (heq ▸ hnz)) heq

/-- Fixed alphabet reindexing or restriction preserves the exact product relation. -/
theorem Compatible.comp {J : Type} {A B : I → K} (h : Compatible A B) (f : J → I) :
    Compatible (A ∘ f) (B ∘ f) := by
  intro xs ys hlen hxs hys heq
  have hx : ∀ i ∈ xs.map f, A i ≠ 0 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hxs j hj
  have hy : ∀ i ∈ ys.map f, A i ≠ 0 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hys j hj
  simpa only [List.map_map] using h (xs.map f) (ys.map f)
    (by simpa using hlen) hx hy (by simpa only [List.map_map] using heq)

end PlanarHom.ProductCompatibility

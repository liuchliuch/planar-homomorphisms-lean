import PlanarHom.PolynomialProductZeros
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# A concrete rational grid with many nonexceptional samples

For `N` samples the grid is exactly `j/(N+1)`, `1 ≤ j ≤ N`.
A finite family of nonzero polynomial certificates bounds the union of
forbidden collisions, and leaves at least `L` good rational samples after
allowing `card(pairs) * D` additional grid points.
-/
noncomputable section
open Set
open scoped BigOperators
namespace PlanarHom.BooleanExceptionalGrid

/-- The explicit rational sample before reducing numerator and denominator. -/
def rationalSample (N j : ℕ) : ℚ := (j : ℚ) / ((N+1 : ℕ) : ℚ)

/-- The rational grid consists of exactly the numerators `1,...,N`. -/
def rationalGrid (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).image (rationalSample N)

theorem rationalSample_injective (N : ℕ) : Function.Injective (rationalSample N) := by
  intro i j hij
  have hden : ((N+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have heq := congrArg (fun q : ℚ => q * ((N+1 : ℕ) : ℚ)) hij
  simp only [rationalSample, div_mul_cancel₀ _ hden] at heq
  exact_mod_cast heq

@[simp] theorem card_rationalGrid (N : ℕ) : (rationalGrid N).card = N := by
  rw [rationalGrid, Finset.card_image_of_injective _ (rationalSample_injective N), Nat.card_Icc]
  omega

theorem mem_rationalGrid_iff {N : ℕ} {q : ℚ} : q ∈ rationalGrid N ↔
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ N ∧ q = (j : ℚ) / ((N+1 : ℕ) : ℚ) := by
  simp only [rationalGrid, Finset.mem_image, Finset.mem_Icc, rationalSample]
  constructor
  · rintro ⟨j, ⟨hj, hjN⟩, rfl⟩
    exact ⟨j, hj, hjN, rfl⟩
  · rintro ⟨j, hj, hjN, rfl⟩
    exact ⟨j, ⟨hj, hjN⟩, rfl⟩

theorem rationalSample_mem_Ioo {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    rationalSample N j ∈ Ioo (0 : ℚ) 1 := by
  have hden : (0 : ℚ) < ((N+1 : ℕ) : ℚ) := by positivity
  constructor
  · exact div_pos (by exact_mod_cast (show 0 < j by omega)) hden
  · apply (div_lt_one hden).mpr
    exact_mod_cast (show j < N+1 by omega)

theorem rationalGrid_subset_Ioo (N : ℕ) : (↑(rationalGrid N) : Set ℚ) ⊆ Ioo (0 : ℚ) 1 := by
  intro q hq
  obtain ⟨j, hj, hjN, rfl⟩ := mem_rationalGrid_iff.mp hq
  exact rationalSample_mem_Ioo hj hjN

theorem rationalGrid_cast_mem_Ioo {N : ℕ} {q : ℚ} (hq : q ∈ rationalGrid N) :
    (q : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h := rationalGrid_subset_Ioo N hq
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Reducing the displayed rational fraction never increases its denominator. -/
theorem rationalSample_den_le (N j : ℕ) : (rationalSample N j).den ≤ N+1 := by
  have heq : rationalSample N j = Rat.divInt (j : ℤ) (N+1 : ℕ) := by
    simp only [rationalSample, Rat.divInt_eq_div, Int.cast_natCast]
  rw [heq, Rat.den_divInt, if_neg (by omega)]
  simpa using Nat.div_le_self (N+1) (Int.gcd (N+1 : ℕ) (j : ℤ))

/-- Both reduced numerator and denominator have the explicit polynomial-size
bounds furnished by the unreduced fraction. -/
theorem rationalGrid_num_den_bounds {N : ℕ} {q : ℚ} (hq : q ∈ rationalGrid N) :
    0 < q.num ∧ q.num.natAbs ≤ N ∧ q.den ≤ N+1 := by
  have hqI := rationalGrid_subset_Ioo N hq
  have hnum : 0 < q.num := Rat.num_pos.mpr hqI.1
  have hlt : q.num < (q.den : ℤ) := by
    simpa using (Rat.lt_iff q 1).mp hqI.2
  have hden : q.den ≤ N+1 := by
    obtain ⟨j, hj, hjN, rfl⟩ := mem_rationalGrid_iff.mp hq
    exact rationalSample_den_le N j
  refine ⟨hnum, ?_, hden⟩
  have hnat : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum.le
  omega

/-- Polynomial zero counting also applies to rational samples, via the
injective embedding of the rationals into the reals. -/
theorem rational_polynomial_zero_card_le (P : Polynomial ℝ) (hP : P ≠ 0)
    (S : Finset ℚ) (hzero : ∀ q ∈ S, P.eval (q : ℝ) = 0) :
    S.card ≤ P.natDegree := by
  have h := PolynomialProductZeros.polynomial_zero_card_le P hP
    (S.image (fun q : ℚ => (q : ℝ))) (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact hzero q hq)
  simpa only [Finset.card_image_of_injective S Rat.cast_injective] using h

/-- The samples on which none of the forbidden indexed collisions occurs. -/
def goodSamples {κ : Type*} (pairs : Finset κ) (collision : κ → ℚ → Prop)
    (S : Finset ℚ) : Finset ℚ := by
  classical
  exact S.filter (fun q => ∀ p ∈ pairs, ¬collision p q)

@[simp] theorem mem_goodSamples {κ : Type*} {pairs : Finset κ} {collision : κ → ℚ → Prop}
    {S : Finset ℚ} {q : ℚ} : q ∈ goodSamples pairs collision S ↔
      q ∈ S ∧ ∀ p ∈ pairs, ¬collision p q := by
  classical
  simp [goodSamples]

/-- The complete exceptional-set union bound from actual nonzero
polynomial certificates, on any finite rational candidate set. -/
theorem card_le_goodSamples_add {κ : Type*} (pairs : Finset κ)
    (collision : κ → ℚ → Prop) (P : κ → Polynomial ℝ) (D : ℕ) (S : Finset ℚ)
    (hP : ∀ p ∈ pairs, P p ≠ 0) (hdegree : ∀ p ∈ pairs, (P p).natDegree ≤ D)
    (hzero : ∀ p ∈ pairs, ∀ q ∈ S, collision p q → (P p).eval (q : ℝ) = 0) :
    S.card ≤ (goodSamples pairs collision S).card + pairs.card * D := by
  classical
  let bad : κ → Finset ℚ := fun p => S.filter (collision p)
  have hbad : ∀ p ∈ pairs, (bad p).card ≤ D := by
    intro p hp
    apply (rational_polynomial_zero_card_le (P p) (hP p hp) (bad p) ?_).trans (hdegree p hp)
    intro q hq
    exact hzero p hp q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
  have hunion : (pairs.biUnion bad).card ≤ pairs.card * D :=
    Finset.card_biUnion_le_card_mul pairs bad D hbad
  have heq : goodSamples pairs collision S = S \ pairs.biUnion bad := by
    ext q
    simp only [mem_goodSamples, Finset.mem_sdiff, Finset.mem_biUnion, bad, Finset.mem_filter]
    aesop
  rw [heq]
  exact Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hunion _)

/-- Taking `B + L` concrete samples, with `B = card(pairs)*D`, leaves at
least `L` nonexceptional rational samples. -/
theorem good_rationalGrid_card_ge {κ : Type*} (pairs : Finset κ)
    (collision : κ → ℚ → Prop) (P : κ → Polynomial ℝ) (D L : ℕ)
    (hP : ∀ p ∈ pairs, P p ≠ 0) (hdegree : ∀ p ∈ pairs, (P p).natDegree ≤ D)
    (hzero : ∀ p ∈ pairs, ∀ q ∈ rationalGrid (pairs.card*D+L),
      collision p q → (P p).eval (q : ℝ) = 0) :
    L ≤ (goodSamples pairs collision (rationalGrid (pairs.card*D+L))).card := by
  have h := card_le_goodSamples_add pairs collision P D
    (rationalGrid (pairs.card*D+L)) hP hdegree hzero
  rw [card_rationalGrid] at h
  omega

/-- The same construction permits any explicit upper bound `B` on the
number of exceptional parameters, for example `N²*D` for `N` products. -/
theorem good_rationalGrid_card_ge_of_bound {κ : Type*} (pairs : Finset κ)
    (collision : κ → ℚ → Prop) (P : κ → Polynomial ℝ) (D B L : ℕ)
    (hB : pairs.card*D ≤ B)
    (hP : ∀ p ∈ pairs, P p ≠ 0) (hdegree : ∀ p ∈ pairs, (P p).natDegree ≤ D)
    (hzero : ∀ p ∈ pairs, ∀ q ∈ rationalGrid (B+L),
      collision p q → (P p).eval (q : ℝ) = 0) :
    L ≤ (goodSamples pairs collision (rationalGrid (B+L))).card := by
  have h := card_le_goodSamples_add pairs collision P D
    (rationalGrid (B+L)) hP hdegree hzero
  rw [card_rationalGrid] at h
  omega

/-- Exactly the requested number of simultaneous nonexceptional rational
samples can be chosen from the concrete bounded grid. -/
theorem exists_good_rational_subgrid {κ : Type*} (pairs : Finset κ)
    (collision : κ → ℚ → Prop) (P : κ → Polynomial ℝ) (D B L : ℕ)
    (hB : pairs.card*D ≤ B)
    (hP : ∀ p ∈ pairs, P p ≠ 0) (hdegree : ∀ p ∈ pairs, (P p).natDegree ≤ D)
    (hzero : ∀ p ∈ pairs, ∀ q ∈ rationalGrid (B+L),
      collision p q → (P p).eval (q : ℝ) = 0) :
    ∃ T : Finset ℚ, T ⊆ rationalGrid (B+L) ∧ T.card = L ∧
      ∀ q ∈ T, ∀ p ∈ pairs, ¬collision p q := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (good_rationalGrid_card_ge_of_bound pairs collision P D B L hB hP hdegree hzero)
  refine ⟨T, ?_, hcard, ?_⟩
  · intro q hq
    exact (mem_goodSamples.mp (hT hq)).1
  · intro q hq
    exact (mem_goodSamples.mp (hT hq)).2

/-- Every selected sample has a positive bounded numerator, positive
bounded denominator, and lies in the real oracle interval. -/
theorem subgrid_sample_bounds {N : ℕ} {T : Finset ℚ}
    (hT : T ⊆ rationalGrid N) {q : ℚ} (hq : q ∈ T) :
    (q : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
      0 < q.num ∧ q.num.natAbs ≤ N ∧ 0 < q.den ∧ q.den ≤ N+1 := by
  have h := rationalGrid_num_den_bounds (hT hq)
  exact ⟨rationalGrid_cast_mem_Ioo (hT hq), h.1, h.2.1, q.den_pos, h.2.2⟩

end PlanarHom.BooleanExceptionalGrid

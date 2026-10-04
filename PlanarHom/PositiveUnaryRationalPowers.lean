import PlanarHom.ProductCompatibility
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Positive unary rational powers in source Lemma 3.1

The target values are genuine `Real.rpow` values. Strict positivity permits every
fixed rational exponent, including negative and zero exponents. Real power
product identities prove the source's exact product-map hypothesis, and the
positive denominator equation proves algebraicity. All original fixed algebraic
constants and all powered unary entries lie in one fixed finite field extension.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PositiveUnaryRationalPowers
open ProductCompatibility
variable {I : Type}

/-- The actual powered unary, with no choice of an algebraic root substituted. -/
def powered (u : I → ℝ) (r : ℚ) : I → ℝ := fun i => (u i) ^ (r : ℝ)

/-- A list of positive unary values has a positive numerical product. -/
theorem product_pos (u : I → ℝ) (hpos : ∀ i, 0 < u i) (xs : List I) :
    0 < (xs.map u).prod := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos (hpos i) ih

/-- Finite products commute with the genuine real power on positive inputs. -/
theorem product_real_rpow (u : I → ℝ) (hpos : ∀ i, 0 < u i) (r : ℝ) (xs : List I) :
    (xs.map (fun i => (u i) ^ r)).prod = ((xs.map u).prod) ^ r := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      have hxs : 0 ≤ (xs.map u).prod := (product_pos u hpos xs).le
      simpa only [List.map_cons, List.prod_cons, ih, Real.mul_rpow (hpos i).le hxs]

/-- Every real exponent preserves numerical product collisions of positive
unary values, and hence in particular every rational exponent does. -/
theorem compatible_real_rpow (u : I → ℝ) (hpos : ∀ i, 0 < u i) (r : ℝ) :
    Compatible u (fun i => (u i) ^ r) := by
  intro xs ys _ _ _ heq
  rw [product_real_rpow u hpos r xs, product_real_rpow u hpos r ys, heq]

/-- The paper's product maps can be given explicitly by the same real power on
numerical products; they are not assumed to be a computable oracle. -/
theorem hasProductMaps_real_rpow (u : I → ℝ) (hpos : ∀ i, 0 < u i) (r : ℝ) :
    HasProductMaps u (fun i => (u i) ^ r) := by
  intro m _
  refine ⟨fun value => value.val ^ r, ?_⟩
  intro xs _ _
  exact (product_real_rpow u hpos r xs).symm

/-- Positive inputs have positive genuine rational powers, including negative powers. -/
theorem powered_pos (u : I → ℝ) (hpos : ∀ i, 0 < u i) (r : ℚ) (i : I) :
    0 < powered u r i := Real.rpow_pos_of_pos (hpos i) r

/-- The numerator/denominator equation holds for the actual real power. -/
theorem real_rpow_rat_den (x : ℝ) (hx : 0 < x) (r : ℚ) :
    (x ^ (r : ℝ)) ^ r.den = x ^ r.num := by
  rw [← Real.rpow_mul_natCast hx.le]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hrat : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hden]
  rw [hrat, Real.rpow_intCast]

/-- Integer powers, including negative powers, preserve algebraicity. -/
theorem isAlgebraic_zpow {x : ℝ} (hx : IsAlgebraic ℚ x) (n : ℤ) :
    IsAlgebraic ℚ (x ^ n) := by
  cases n with
  | ofNat n => simpa using hx.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hx.pow (n + 1)).inv

/-- Rational real powers of positive algebraic numbers are algebraic, proved
from a positive-degree power equation rather than an assumed root selection. -/
theorem isAlgebraic_real_rpow_rat {x : ℝ} (hpos : 0 < x) (hAlg : IsAlgebraic ℚ x) (r : ℚ) :
    IsAlgebraic ℚ (x ^ (r : ℝ)) := by
  apply IsAlgebraic.of_pow r.den_pos
  rw [real_rpow_rat_den x hpos r]
  exact isAlgebraic_zpow hAlg r.num

/-- All scalar hypotheses of the explicit positive-unary rational-power
consequence of Lemma 3.1, derived simultaneously. -/
theorem powered_spec (u : I → ℝ) (hpos : ∀ i, 0 < u i)
    (hAlg : ∀ i, IsAlgebraic ℚ (u i)) (r : ℚ) :
    (∀ i, 0 < powered u r i) ∧ (∀ i, IsAlgebraic ℚ (powered u r i)) ∧
      (∀ i, u i = 0 → powered u r i = 0) ∧
      Compatible u (powered u r) ∧ HasProductMaps u (powered u r) := by
  refine ⟨powered_pos u hpos r, fun i => isAlgebraic_real_rpow_rat (hpos i) (hAlg i) r, ?_,
    compatible_real_rpow u hpos r, hasProductMaps_real_rpow u hpos r⟩
  intro i hz
  exact ((ne_of_gt (hpos i)) hz).elim

/-- Every finite collection of original fixed algebraic constants and powered
unary entries fits in one actual finite extension of the rationals. The extension
is fixed by these constants and the fixed exponent, independently of any input instance. -/
theorem exists_fixed_finite_extension [Finite I] (u : I → ℝ) (hpos : ∀ i, 0 < u i)
    (hAlg : ∀ i, IsAlgebraic ℚ (u i)) (r : ℚ) (S : Set ℝ) (hS : S.Finite)
    (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      ∀ i, u i ∈ K ∧ powered u r i ∈ K := by
  let T : Set ℝ := S ∪ Set.range u ∪ Set.range (powered u r)
  have hT : T.Finite := (hS.union (Set.finite_range u)).union (Set.finite_range (powered u r))
  letI := hT.fintype
  let K := IntermediateField.adjoin ℚ T
  have hTAlg : ∀ x ∈ T, IsAlgebraic ℚ x := by
    intro x hx
    rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · exact hSAlg x hx
    · exact hAlg i
    · exact isAlgebraic_real_rpow_rat (hpos i) (hAlg i) r
  have hdim : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => (hTAlg x hx).isIntegral)
  refine ⟨K, hdim, ?_, ?_⟩
  · intro x hx
    exact IntermediateField.subset_adjoin ℚ T (Or.inl (Or.inl hx))
  · intro i
    exact ⟨IntermediateField.subset_adjoin ℚ T (Or.inl (Or.inr ⟨i, rfl⟩)),
      IntermediateField.subset_adjoin ℚ T (Or.inr ⟨i, rfl⟩)⟩

end PlanarHom.PositiveUnaryRationalPowers

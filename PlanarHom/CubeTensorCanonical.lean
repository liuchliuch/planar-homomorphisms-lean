import PlanarHom.CubeTensorFactors

/-!
# Canonical normalized cube factors

The explicit factors in Proposition 4.8 are recovered from the original matrix
alone: the reference diagonal, its single-bit neighbor entries, and the
single-bit diagonal entries. The statements below identify those matrices with
the proved normalized tensor factors, including positivity and algebraicity.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem oneCoordinate_false (r : ι) : oneCoordinate r false = zeroColor := by
  funext k
  by_cases hk : k = r
  · subst k; simp [oneCoordinate, zeroColor]
  · simp [oneCoordinate, Function.update_of_ne hk, zeroColor]

/-- The exact symmetric two-by-two ratio matrix stated in Proposition 4.8. -/
def canonicalFactor (N : Matrix (ι → Bool) (ι → Bool) ℝ) (r : ι) : Matrix Bool Bool ℝ :=
  fun a b => if a then
    (if b then N (oneCoordinate r true) (oneCoordinate r true) / N zeroColor zeroColor
      else N zeroColor (oneCoordinate r true) / N zeroColor zeroColor)
    else (if b then N zeroColor (oneCoordinate r true) / N zeroColor zeroColor else 1)

/-- The canonical ratios are precisely the original normalized local factors. -/
theorem normalizedFactor_eq_canonical (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (hHerm : N.IsHermitian) (γ : ℝ) (F : ι → Matrix Bool Bool ℝ)
    (hN : N = γ • tensor F) (hγ : γ ≠ 0) (hdiag : ∀ r, F r false false ≠ 0) (r : ι) :
    normalizedFactor F r = canonicalFactor N r := by
  ext a b
  cases a <;> cases b
  · exact normalizedFactor_zero_zero F hdiag r
  · simpa only [canonicalFactor, Bool.false_eq_true, ite_false,
      ite_true, oneCoordinate_false] using
      normalizedFactor_eq_entry_ratio N γ F hN hγ hdiag r false true
  · have hs : N (oneCoordinate r true) zeroColor = N zeroColor (oneCoordinate r true) := by
      simpa only [star_trivial] using hHerm.apply zeroColor (oneCoordinate r true)
    simpa only [canonicalFactor, Bool.false_eq_true, ite_false,
      ite_true, oneCoordinate_false, hs] using
      normalizedFactor_eq_entry_ratio N γ F hN hγ hdiag r true false
  · exact normalizedFactor_eq_entry_ratio N γ F hN hγ hdiag r true true

/-- The normalized scalar and every factor are recovered from the original matrix. -/
theorem tensor_eq_canonical_factors (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (hHerm : N.IsHermitian) (γ : ℝ) (F : ι → Matrix Bool Bool ℝ)
    (hN : N = γ • tensor F) (hγ : γ ≠ 0) (hdiag : ∀ r, F r false false ≠ 0) :
    N = N zeroColor zeroColor • tensor (canonicalFactor N) := by
  have heq : normalizedFactor F = canonicalFactor N := funext fun r =>
    normalizedFactor_eq_canonical N hHerm γ F hN hγ hdiag r
  rw [← heq]
  exact scalar_tensor_eq_reference_smul_normalized N γ F hN hdiag

/-- Canonical factor entries are algebraic whenever the original entries are algebraic. -/
theorem canonicalFactor_isAlgebraic (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (hAlg : ∀ z w, IsAlgebraic ℚ (N z w)) (r : ι) (a b : Bool) :
    IsAlgebraic ℚ (canonicalFactor N r a b) := by
  cases a <;> cases b <;> simp only [canonicalFactor, ite_true, ite_false,
    Bool.false_eq_true]
  · exact isAlgebraic_one
  all_goals
    rw [div_eq_mul_inv]
    exact (hAlg _ _).mul (hAlg _ _).inv

/-- The canonical factors are PD and strictly positive for a connected
nonnegative tensor of PD local matrices. -/
theorem canonicalFactor_posDef_and_pos (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (hHerm : N.IsHermitian) (γ : ℝ) (F : ι → Matrix Bool Bool ℝ)
    (hN : N = γ • tensor F) (hγ : 0 < γ) (hF : ∀ r, (F r).PosDef)
    (hnonneg : ∀ z w, 0 ≤ N z w)
    (hconn : (LogarithmicSupport.offDiagonalSupport N hHerm).Connected) (r : ι) :
    (canonicalFactor N r).PosDef ∧ ∀ a b, 0 < canonicalFactor N r a b := by
  have hdiag : ∀ r, F r false false ≠ 0 := fun r =>
    ne_of_gt (posDef_diagonal_pos _ (hF r) false)
  rw [← normalizedFactor_eq_canonical N hHerm γ F hN (ne_of_gt hγ) hdiag r]
  exact ⟨normalizedFactor_posDef F hF r,
    normalizedFactor_entry_pos_of_connected N hHerm γ F hN hγ hF hnonneg hconn r⟩

end PlanarHom.CubeTensorExponential

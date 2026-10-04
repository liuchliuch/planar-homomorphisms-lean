import PlanarHom.CubeTensorNormalization
import PlanarHom.LogarithmicSupport

/-!
# Positive normalized factors of a connected nonnegative tensor matrix

Nonnegativity transfers to each local factor. A zero off-diagonal local factor
would separate the full nonzero-support graph by that coordinate; connectedness
therefore makes every local entry strictly positive. Positive definiteness and
ratio normalization are proved on the actual two-by-two factors.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal entries of a real positive-definite matrix are strictly positive. -/
theorem posDef_diagonal_pos {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosDef) (i : V) : 0 < A i i := by
  have hx : (Pi.single i (1 : ℝ) : V → ℝ) ≠ 0 := by
    intro hz
    have h := congrFun hz i
    simpa using h
  simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct,
    one_mul, Matrix.col_apply] using hA.2 (Pi.single i 1) hx

/-- The full reference diagonal is positive when the scalar and local reference diagonals are. -/
theorem reference_entry_pos (N : Matrix (ι → Bool) (ι → Bool) ℝ) (γ : ℝ)
    (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : 0 < γ) (hdiag : ∀ r, 0 < F r false false) : 0 < N zeroColor zeroColor := by
  rw [hN]
  exact mul_pos hγ (Finset.prod_pos fun r _ => hdiag r)

/-- Nonnegative full-matrix entries force every local factor entry nonnegative. -/
theorem factor_entry_nonneg (N : Matrix (ι → Bool) (ι → Bool) ℝ) (γ : ℝ)
    (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : 0 < γ) (hdiag : ∀ r, 0 < F r false false)
    (hnonneg : ∀ z w, 0 ≤ N z w) (r : ι) (a b : Bool) : 0 ≤ F r a b := by
  have hp : 0 < ∏ k ∈ Finset.univ.erase r, F k false false :=
    Finset.prod_pos fun k _ => hdiag k
  have h := hnonneg (oneCoordinate r a) (oneCoordinate r b)
  rw [hN] at h
  simp only [Matrix.smul_apply, smul_eq_mul, tensor_oneCoordinate] at h
  exact (mul_nonneg_iff_of_pos_right hp).mp ((mul_nonneg_iff_of_pos_left hγ).mp h)

/-- A zero local off-diagonal would force every full support edge to preserve that bit. -/
theorem factor_offDiagonal_ne_zero_of_connected
    (N : Matrix (ι → Bool) (ι → Bool) ℝ) (hNherm : N.IsHermitian)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hsym : ∀ r a b, F r a b = F r b a)
    (hconn : (LogarithmicSupport.offDiagonalSupport N hNherm).Connected) (r : ι) :
    F r false true ≠ 0 := by
  intro hzero
  have hback : F r true false = 0 := (hsym r true false).trans hzero
  let G := LogarithmicSupport.offDiagonalSupport N hNherm
  have hpreserve : ∀ z w : ι → Bool, G.Adj z w → z r = w r := by
    intro z w hadj
    by_contra hne
    have hlocal : F r (z r) (w r) = 0 := by
      cases hz : z r <;> cases hw : w r
      · exact (hne (hz.trans hw.symm)).elim
      · simpa only [hz, hw] using hzero
      · simpa only [hz, hw] using hback
      · exact (hne (hz.trans hw.symm)).elim
    have htensor : tensor F z w = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) hlocal
    have hzN : N z w = 0 := by rw [hN]; simp [htensor]
    exact hadj.2 hzN
  have hwalk : ∀ {z w : ι → Bool}, G.Walk z w → z r = w r := by
    intro z w p
    induction p with
    | nil => rfl
    | @cons z v w hzv p ih => exact (hpreserve z v hzv).trans ih
  obtain ⟨p, hp⟩ := hconn.exists_isPath zeroColor (oneCoordinate r true)
  have hbad := hwalk p
  simpa [zeroColor, oneCoordinate] using hbad

/-- Connected nonnegative tensors with positive-definite symmetric factors
have strictly positive local entries. -/
theorem factor_entry_pos_of_connected
    (N : Matrix (ι → Bool) (ι → Bool) ℝ) (hNherm : N.IsHermitian)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : 0 < γ) (hF : ∀ r, (F r).PosDef)
    (hnonneg : ∀ z w, 0 ≤ N z w)
    (hconn : (LogarithmicSupport.offDiagonalSupport N hNherm).Connected)
    (r : ι) (a b : Bool) : 0 < F r a b := by
  have hdiag : ∀ r, 0 < F r false false := fun r => posDef_diagonal_pos _ (hF r) false
  have hsym : ∀ r a b, F r a b = F r b a := by
    intro r a b
    simpa only [star_trivial] using ((hF r).1.apply b a)
  have hoff : 0 < F r false true := by
    have hn := factor_entry_nonneg N γ F hN hγ hdiag hnonneg r false true
    have hne := factor_offDiagonal_ne_zero_of_connected N hNherm γ F hN hsym hconn r
    exact lt_of_le_of_ne hn (Ne.symm hne)
  cases a <;> cases b
  · exact hdiag r
  · exact hoff
  · rw [hsym r true false]; exact hoff
  · exact posDef_diagonal_pos _ (hF r) true

/-- Positive normalization preserves positive definiteness. -/
theorem normalizedFactor_posDef (F : ι → Matrix Bool Bool ℝ)
    (hF : ∀ r, (F r).PosDef) (r : ι) : (normalizedFactor F r).PosDef := by
  exact (hF r).smul (inv_pos.mpr (posDef_diagonal_pos _ (hF r) false))

/-- Normalized factors are strictly positive whenever the full tensor support is connected. -/
theorem normalizedFactor_entry_pos_of_connected
    (N : Matrix (ι → Bool) (ι → Bool) ℝ) (hNherm : N.IsHermitian)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : 0 < γ) (hF : ∀ r, (F r).PosDef)
    (hnonneg : ∀ z w, 0 ≤ N z w)
    (hconn : (LogarithmicSupport.offDiagonalSupport N hNherm).Connected)
    (r : ι) (a b : Bool) : 0 < normalizedFactor F r a b := by
  exact mul_pos (inv_pos.mpr (posDef_diagonal_pos _ (hF r) false))
    (factor_entry_pos_of_connected N hNherm γ F hN hγ hF hnonneg hconn r a b)

end PlanarHom.CubeTensorExponential

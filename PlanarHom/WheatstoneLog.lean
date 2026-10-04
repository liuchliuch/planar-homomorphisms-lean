import PlanarHom.WheatstoneExpansion
import PlanarHom.PolynomialMatrixLog
import PlanarHom.SchurExponentialLog
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# The actual logarithmic Wheatstone expansion

The exact coefficient calculations are transferred to the genuine spectral
matrix logarithm. This proves the analytic obstruction in Lemma 4.4 without
assuming a formal logarithm series or its coefficients.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics

namespace PlanarHom.WheatstoneCoefficients
open MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual five-edge Wheatstone signature evaluated at the graph-distance kernel. -/
def wheatstoneMatrix (G : SimpleGraph V) (t : ℝ) : Matrix V V ℝ :=
  polynomialMatrixEval (polynomialMatrix G) t

omit [DecidableEq V] in
/-- The polynomial-matrix representation is exactly the actual internal-color sum. -/
theorem wheatstoneMatrix_apply (G : SimpleGraph V) (t : ℝ) (i j : V) :
    wheatstoneMatrix G t i j = ∑ a : V, ∑ b : V,
      EntropyCompletion.distanceKernel G t i a * EntropyCompletion.distanceKernel G t a j *
      EntropyCompletion.distanceKernel G t i b * EntropyCompletion.distanceKernel G t b j *
      EntropyCompletion.distanceKernel G t a b := polynomial_eval G i j t

omit [DecidableEq V] in
/-- Its symmetry is exact, at every real parameter. -/
theorem wheatstoneMatrix_isHermitian (G : SimpleGraph V) (t : ℝ) :
    (wheatstoneMatrix G t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((polynomial G j i).eval t) = (polynomial G i j).eval t
  rw [star_trivial, polynomial_symm G j i]

/-- Evaluation commutes with subtracting the identity. -/
theorem perturbation_eval (G : SimpleGraph V) (t : ℝ) :
    polynomialMatrixEval (perturbationPolynomial G) t = wheatstoneMatrix G t - 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [polynomialMatrixEval, perturbationPolynomial, polynomialMatrix, wheatstoneMatrix, hij]

/-- Restoring the identity gives the exact Wheatstone matrix. -/
theorem one_add_perturbation_eval (G : SimpleGraph V) (t : ℝ) :
    1 + polynomialMatrixEval (perturbationPolynomial G) t = wheatstoneMatrix G t := by
  rw [perturbation_eval]
  abel

/-- At distance two, every coefficient below degree four vanishes. -/
theorem perturbation_distance_two_coeff_lt_four (G : SimpleGraph V) (hc : G.Connected)
    {i j : V} (hd : G.dist i j = 2) (k : ℕ) (hk : k < 4) :
    (perturbationPolynomial G i j).coeff k = 0 := by
  by_cases hk0 : k = 0
  · subst k; exact perturbation_coeff_zero G hc i j
  · rw [perturbation_coeff_pos G i j hk0]
    exact coeff_eq_zero_of_lt_twice_dist G hc i j (by omega)

/-- The precise analytic obstruction in Lemma 4.4:
`log Ω(E(t))ᵢⱼ = 2 ε t⁵ + O(t⁶)` for a distance-two pair with exactly two
common neighbors, where ε records whether those neighbors are adjacent. -/
theorem matrixLog_wheatstone_distance_two_leading_isBigO (G : SimpleGraph V)
    (hc : G.Connected) {i j u v : V} (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    (fun t : ℝ => EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j -
      (if G.Adj u v then 2 else 0) * t ^ 5) =O[𝓝 0] (fun t : ℝ => t ^ 6) := by
  letI : Nonempty V := hc.nonempty
  let p : Polynomial ℝ := Polynomial.C (if G.Adj u v then 2 else 0) * Polynomial.X ^ 5
  have hherm : ∀ᶠ t in 𝓝 (0 : ℝ),
      (polynomialMatrixEval (perturbationPolynomial G) t).IsHermitian :=
    Eventually.of_forall fun t => by
      rw [perturbation_eval]
      exact (wheatstoneMatrix_isHermitian G t).sub Matrix.isHermitian_one
  have hmatch : ∀ k < 6,
      (perturbationPolynomial G i j).coeff k -
        (2 : ℝ)⁻¹ * ((perturbationPolynomial G ^ 2) i j).coeff k = p.coeff k := by
    intro k hk
    by_cases hlo : k < 4
    · rw [perturbation_distance_two_coeff_lt_four G hc hd k hlo,
        perturbation_square_coeff_lt_four G hc i j k hlo]
      simp [p, show k ≠ 5 by omega]
    · have hcases : k = 4 ∨ k = 5 := by omega
      rcases hcases with rfl | rfl
      · rw [perturbation_coeff_pos G i j (by decide), coeff_four_eq_four G hc hd huv hcommon,
          perturbation_square_coeff_four G hc huv hcommon]
        norm_num [p, Polynomial.coeff_C_mul_X_pow]
      · rw [perturbation_coeff_pos G i j (by decide), coeff_five_eq_eight_add G hc hd huv hcommon,
          perturbation_square_coeff_five G hc hd huv hcommon]
        norm_num [p, Polynomial.coeff_C_mul_X_pow]
  have h := matrixLog_polynomial_entry_sub_eval_isBigO (perturbationPolynomial G)
    (perturbation_coeff_lt_two G hc) hherm i j p hmatch
  simpa only [one_add_perturbation_eval, p, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using h

/-- Adjacent common neighbors force a new positive logarithmic nonedge for every
sufficiently small positive real parameter, not merely a nonzero formal coefficient. -/
theorem eventually_matrixLog_wheatstone_pos (G : SimpleGraph V) (hc : G.Connected)
    {i j u v : V} (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v)
    (ha : G.Adj u v) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, 0 < EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j := by
  letI : Nonempty V := hc.nonempty
  apply eventually_pos_of_positive_leading (a := (2 : ℝ)) (by norm_num) 5
  simpa only [if_pos ha] using matrixLog_wheatstone_distance_two_leading_isBigO G hc hd huv hcommon

/-- The exact Wheatstone matrix is the identity at zero. -/
theorem wheatstoneMatrix_zero (G : SimpleGraph V) (hc : G.Connected) :
    wheatstoneMatrix G 0 = 1 := by
  ext i j
  simp [wheatstoneMatrix, polynomialMatrixEval, polynomialMatrix, ← Polynomial.coeff_zero_eq_eval_zero,
    coeff_zero G hc, Matrix.one_apply]

omit [DecidableEq V] in
/-- Every entry is polynomial, hence the actual matrix curve is continuous. -/
theorem continuous_wheatstoneMatrix (G : SimpleGraph V) : Continuous (wheatstoneMatrix G) := by
  apply continuous_matrix
  intro i j
  exact (polynomial G i j).continuous

/-- Strict row diagonal dominance with positive margins gives actual positive
 definiteness for a Hermitian real matrix. -/
theorem posDef_of_rowSum_lt_diagonal {H : Matrix V V ℝ} (hH : H.IsHermitian)
    (hs : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖H i j‖ < H i i) : H.PosDef := by
  apply hH.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' H) (hH.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (hH.eigenvectorBasis i : V → ℝ))
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · exact hH.mulVec_eigenvectorBasis i
    · intro hz
      apply hH.eigenvectorBasis.orthonormal.ne_zero i
      ext j
      exact congrFun hz j
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  have hk' : |hH.eigenvalues i - H k k| < H k k := by
    apply lt_of_le_of_lt _ (hs k)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hk
  have := (abs_lt.mp hk').1
  linarith

/-- Initial positive definiteness of the actual Wheatstone signature. -/
theorem eventually_posDef_wheatstoneMatrix (G : SimpleGraph V) (hc : G.Connected) :
    ∀ᶠ t : ℝ in 𝓝 0, (wheatstoneMatrix G t).PosDef := by
  have he (i : V) : ∀ᶠ t : ℝ in 𝓝 0,
      (∑ j ∈ Finset.univ.erase i, ‖wheatstoneMatrix G t i j‖) < wheatstoneMatrix G t i i := by
    have hsum : Continuous (fun t : ℝ => ∑ j ∈ Finset.univ.erase i,
        ‖wheatstoneMatrix G t i j‖) :=
      continuous_finset_sum _ (fun j _ => ((continuous_wheatstoneMatrix G).matrix_elem i j).norm)
    apply Filter.Tendsto.eventually_lt hsum.continuousAt
      ((continuous_wheatstoneMatrix G).matrix_elem i i).continuousAt
    have hs0 : (∑ j ∈ Finset.univ.erase i, ‖wheatstoneMatrix G 0 i j‖) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      simp [wheatstoneMatrix_zero G hc, hij]
    change (∑ j ∈ Finset.univ.erase i, ‖wheatstoneMatrix G 0 i j‖) < wheatstoneMatrix G 0 i i
    rw [hs0, wheatstoneMatrix_zero G hc]
    norm_num
  filter_upwards [Filter.eventually_all.mpr he] with t ht
  exact posDef_of_rowSum_lt_diagonal (wheatstoneMatrix_isHermitian G t) ht

omit [DecidableEq V] in
/-- Every entry of the signature is positive at every positive real parameter. -/
theorem wheatstoneMatrix_entry_pos (G : SimpleGraph V) (hc : G.Connected)
    {t : ℝ} (ht : 0 < t) (i j : V) : 0 < wheatstoneMatrix G t i j := by
  letI : Nonempty V := hc.nonempty
  rw [wheatstoneMatrix_apply]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro a _
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro b _
  unfold EntropyCompletion.distanceKernel
  exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos ht _) (pow_pos ht _))
    (pow_pos ht _)) (pow_pos ht _)) (pow_pos ht _)

/-- Actual perturbation is of operator order two. -/
theorem perturbation_eval_isBigO_two (G : SimpleGraph V) (hc : G.Connected) :
    polynomialMatrixEval (perturbationPolynomial G) =O[𝓝 0] (fun t : ℝ => t ^ 2) :=
  polynomial_matrix_eval_isBigO_pow _ 2 (perturbation_coeff_lt_two G hc)

/-- On an edge, the actual logarithmic expansion is `2t² + 2t³ + O(t⁴)`. -/
theorem matrixLog_wheatstone_edge_leading_isBigO (G : SimpleGraph V) (hc : G.Connected)
    {i j : V} (hij : G.Adj i j) :
    (fun t : ℝ => EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j -
      (2 * t ^ 2 + 2 * t ^ 3)) =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
  letI : Nonempty V := hc.nonempty
  let P := perturbationPolynomial G
  have ho := perturbation_eval_isBigO_two G hc
  have hz : Tendsto (polynomialMatrixEval P) (𝓝 0) (𝓝 0) :=
    ho.trans_tendsto (by simpa using (continuous_pow 2).tendsto (0 : ℝ))
  have hh : ∀ᶠ t in 𝓝 (0 : ℝ), (polynomialMatrixEval P t).IsHermitian :=
    Eventually.of_forall fun t => by
      rw [show P = perturbationPolynomial G from rfl, perturbation_eval]
      exact (wheatstoneMatrix_isHermitian G t).sub Matrix.isHermitian_one
  have hlog := entry_isBigO (matrixLog_sub_logTaylor_isBigO_pow
    (polynomialMatrixEval P) hh hz 2 1 ho) i j
  let p : Polynomial ℝ := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X ^ 3
  have hm : ∀ k < 4, (P i j).coeff k = p.coeff k := by
    intro k hk
    interval_cases k
    · simp [P, p, perturbation_coeff_zero G hc]
    · simp [P, p, perturbation_coeff_one G hc]
    · rw [show P = perturbationPolynomial G from rfl, perturbation_coeff_pos G i j (by decide),
        edge_coeff_two G hc hij]
      norm_num [p]
    · rw [show P = perturbationPolynomial G from rfl, perturbation_coeff_pos G i j (by decide),
        edge_coeff_three G hc hij]
      norm_num [p]
  have hpoly := polynomial_eval_sub_isBigO_pow (P i j) p 4 hm
  have hl : (fun t : ℝ => EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j -
      (P i j).eval t) =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
    simpa only [logTaylor_one, P, one_add_perturbation_eval, Matrix.sub_apply,
      polynomialMatrixEval, Nat.reduceAdd, Nat.reduceMul] using hlog
  have h := hl.add hpoly
  simpa [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, sub_add_sub_cancel] using h

/-- Every original graph edge stays positive in the logarithmic Wheatstone support. -/
theorem eventually_matrixLog_wheatstone_edge_pos (G : SimpleGraph V) (hc : G.Connected)
    {i j : V} (hij : G.Adj i j) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, 0 < EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j := by
  letI : Nonempty V := hc.nonempty
  have h := (matrixLog_wheatstone_edge_leading_isBigO G hc hij).trans
    (pow_isBigO_pow (show 3 ≤ 4 by decide))
  have hterm : (fun t : ℝ => 2 * t ^ 3) =O[𝓝 0] (fun t : ℝ => t ^ 3) :=
    (isBigO_refl _ _).const_mul_left 2
  apply eventually_pos_of_positive_leading (a := (2 : ℝ)) (by norm_num) 2
  convert h.add hterm using 1
  funext t
  ring

end PlanarHom.WheatstoneCoefficients

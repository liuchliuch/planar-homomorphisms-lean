import PlanarHom.MatrixEntryAsymptotics

/-!
# Actual leading coefficients for Schur powers of matrix exponentials

This proves the analytic expansion used in Lemmas 4.1 and 4.3 for the genuine
matrix exponential and the genuine spectral logarithm. No leading coefficient
or order assertion is included among the hypotheses.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The usual matrix exponential Taylor polynomial along a scalar line. -/
def expTaylor (L : Matrix V V ℝ) (n : ℕ) (t : ℝ) : Matrix V V ℝ :=
  ∑ k ∈ Finset.range n, (t ^ k / (k.factorial : ℝ)) • L ^ k

/-- Arbitrary-order Taylor expansion of the genuine matrix exponential. -/
theorem exp_sub_expTaylor_isBigO (L : Matrix V V ℝ) (n : ℕ) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • L) - expTaylor L n t) =O[𝓝 0]
      (fun t : ℝ => t ^ n) := by
  let F : ℝ →L[ℝ] Matrix V V ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight L
  have hF : Tendsto F (𝓝 0) (𝓝 0) := by simpa using F.continuous.tendsto (0 : ℝ)
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ)
    (𝔸 := Matrix V V ℝ)).isBigO_sub_partialSum_pow n
  have hcomp := h.comp_tendsto hF
  have hbound := (F.isBigO_id (𝓝 0)).norm_left.pow n
  have hresult := hcomp.trans hbound
  convert hresult using 1
  funext t
  simp only [Function.comp_apply, F, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, zero_add, expTaylor, FormalMultilinearSeries.partialSum,
    NormedSpace.expSeries_apply_eq, smul_pow, smul_smul, div_eq_mul_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

/-- First-order exponential expansion with a quadratic remainder. -/
theorem exp_sub_one_sub_linear_isBigO (L : Matrix V V ℝ) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • L) - (1 + t • L)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  simpa [expTaylor, Finset.sum_range_succ] using exp_sub_expTaylor_isBigO L 2

/-- Matrix exponentiation is a first-order perturbation of the identity. -/
theorem exp_sub_one_isBigO (L : Matrix V V ℝ) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • L) - 1) =O[𝓝 0]
      (fun t : ℝ => t) := by
  have hrem := (exp_sub_one_sub_linear_isBigO L).trans
    (pow_isBigO_pow (show 1 ≤ 2 by omega))
  have hlin : (fun t : ℝ => t • L) =O[𝓝 0] (fun t : ℝ => t) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight L).isBigO_id (𝓝 0)
  simp only [pow_one] at hrem
  have h := hrem.add hlin
  simpa only [sub_add_eq_sub_sub, sub_add_cancel] using h

/-- Off-diagonal exponential entries have their actual linear coefficient. -/
theorem exp_entry_sub_linear_isBigO (L : Matrix V V ℝ) (i j : V) (hij : i ≠ j) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • L) i j - L i j * t) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  have h := entry_isBigO (exp_sub_one_sub_linear_isBigO L) i j
  simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hij,
    Matrix.smul_apply, smul_eq_mul, zero_add, mul_comm] using h

/-- Entrywise powers of the actual exponential. -/
def schurExp (L : Matrix V V ℝ) (s : ℕ) (t : ℝ) : Matrix V V ℝ :=
  fun i j => (NormedSpace.exp ℝ (t • L) i j) ^ s

/-- Every off-diagonal Schur-exponential entry has order at least `s`. -/
theorem schurExp_entry_isBigO (L : Matrix V V ℝ) (s : ℕ) (i j : V) (hij : i ≠ j) :
    (fun t => schurExp L s t i j) =O[𝓝 0] (fun t : ℝ => t ^ s) := by
  have he : (fun t : ℝ => NormedSpace.exp ℝ (t • L) i j) =O[𝓝 0]
      (fun t : ℝ => t) := by
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] using
      entry_isBigO (exp_sub_one_isBigO L) i j
  exact he.pow s

/-- The actual coefficient of degree `s` in every off-diagonal Schur power. -/
theorem schurExp_entry_sub_leading_isBigO (L : Matrix V V ℝ) (s : ℕ)
    (i j : V) (hij : i ≠ j) :
    (fun t => schurExp L s t i j - (L i j) ^ s * t ^ s) =O[𝓝 0]
      (fun t : ℝ => t ^ (s + 1)) := by
  apply pow_sub_leading_isBigO
  · simpa only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] using
      entry_isBigO (exp_sub_one_isBigO L) i j
  · exact exp_entry_sub_linear_isBigO L i j hij

/-- The Schur power remains a first-order perturbation on its diagonal. -/
theorem schurExp_sub_one_isBigO (L : Matrix V V ℝ) (s : ℕ) (hs : 0 < s) :
    (fun t => schurExp L s t - 1) =O[𝓝 0] (fun t : ℝ => t) := by
  apply matrix_isBigO_of_entries
  intro i j
  by_cases hij : i = j
  · subst j
    have hd : DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ℝ (t • L) i i) 0 :=
      (entryCLM i i).differentiableAt.comp 0
        (hasFDerivAt_exp_smul_const ℝ L (0 : ℝ)).differentiableAt
    simpa [schurExp] using (hd.pow s).hasFDerivAt.isBigO_sub
  · have h := (schurExp_entry_isBigO L s i j hij).trans
      (pow_isBigO_pow (show 1 ≤ s from hs))
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, pow_one] using h

/-- Schur powers of a Hermitian exponential are Hermitian for every real parameter. -/
theorem schurExp_isHermitian (L : Matrix V V ℝ) (hL : L.IsHermitian) (s : ℕ) (t : ℝ) :
    (schurExp L s t).IsHermitian := by
  have hLs : IsSelfAdjoint (t • L) := by
    change star (t • L) = t • L
    rw [star_smul, star_trivial]
    exact congrArg (fun A : Matrix V V ℝ => t • A) hL
  have he : (NormedSpace.exp ℝ (t • L)).IsHermitian := hLs.exp ℝ
  ext i j
  simpa only [Matrix.conjTranspose_apply, schurExp, star_trivial] using
    congrArg (fun x : ℝ => x ^ s) (he.apply i j)

variable [Nonempty V]

/-- The expansion from Lemmas 4.1 and 4.3: for distinct indices,
`log((exp(tL))◦s)ᵢⱼ = t^s Lᵢⱼ^s + O(t^(s+1))`.
In fact, the analytic expansion holds for every positive integer `s`; evenness
is needed only for positivity in the paper's separate matrix-family argument. -/
theorem matrixLog_schurExp_entry_sub_leading_isBigO (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (s : ℕ) (hs : 0 < s) (i j : V) (hij : i ≠ j) :
    (fun t => EntropyCompletion.matrixLog (schurExp L s t) i j -
      (L i j) ^ s * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
  let Q : ℝ → Matrix V V ℝ := fun t => schurExp L s t - 1
  have hQ : Q =O[𝓝 0] (fun t : ℝ => t) := schurExp_sub_one_isBigO L s hs
  have hzero : Tendsto Q (𝓝 0) (𝓝 0) := hQ.trans_tendsto tendsto_id
  have hherm : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian := Eventually.of_forall fun t =>
    (schurExp_isHermitian L hL s t).sub Matrix.isHermitian_one
  have hoff : ∀ a b, a ≠ b → (fun t => Q t a b) =O[𝓝 0] (fun t : ℝ => t ^ s) := by
    intro a b hab
    simpa only [Q, Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] using
      schurExp_entry_isBigO L s a b hab
  have hlog := matrixLog_sub_self_offDiagonal_isBigO Q s hs hherm hzero hQ hoff i j hij
  have hlead := schurExp_entry_sub_leading_isBigO L s i j hij
  have hlog' : (fun t => EntropyCompletion.matrixLog (schurExp L s t) i j -
      schurExp L s t i j) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
    have heq : ∀ t, 1 + (schurExp L s t - 1) = schurExp L s t := by intro t; abel
    simpa only [Q, heq, Matrix.sub_apply, Matrix.one_apply_ne hij,
      sub_zero] using hlog
  have h := hlog'.add hlead
  simpa only [sub_add_sub_cancel] using h

/-- A positive leading real coefficient forces positivity at all sufficiently
small positive real parameters. -/
theorem eventually_pos_of_positive_leading {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (s : ℕ)
    (hrem : (fun t => f t - a * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1))) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, 0 < f t := by
  obtain ⟨C, hC, hbound⟩ := hrem.exists_pos
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t < a / C := eventually_lt_nhds (div_pos ha hC)
  filter_upwards [hbound.bound.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hb ht hpos
  have htpos : 0 < t := hpos
  have hpow : 0 < t ^ s := pow_pos htpos s
  have hCt : C * t < a := by
    have hh := (lt_div_iff₀ hC).mp ht
    simpa only [mul_comm] using hh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos htpos (s + 1))] at hb
  have hlo := (abs_le.mp hb).1
  rw [pow_succ] at hlo
  nlinarith [mul_lt_mul_of_pos_right hCt hpow]

/-- Positive even Schur powers make every nonzero logarithmic edge positive,
as asserted by the analytic part of Lemma 4.1. -/
theorem eventually_matrixLog_schurExp_entry_pos (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (s : ℕ) (hs : 0 < s) (heven : Even s)
    (i j : V) (hij : i ≠ j) (hne : L i j ≠ 0) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, 0 < EntropyCompletion.matrixLog (schurExp L s t) i j :=
  eventually_pos_of_positive_leading (heven.pow_pos hne) s
    (matrixLog_schurExp_entry_sub_leading_isBigO L hL s hs i j hij)

end PlanarHom.MatrixLogCoefficients

import PlanarHom.EntropyCompletion
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-!
# Coercivity of the genuine matrix-exponential dual

The dual objective is `Tr(exp C) - Tr(CP)` on real symmetric matrices.
For every positive-definite `P`, this file proves quantitative coercivity,
compactness of every symmetric sublevel set, and existence of a minimizer on
any nonempty closed symmetric set. The graph-completion application uses
`P = (1 - x) I + x J`, which is positive definite for `0 ≤ x < 1`.

The exponential is the actual `NormedSpace.exp` power series. Its spectral
formula is obtained from the proved CFC bridge, and no entropy-interiority,
coercivity, or optimizer existence assumption is used.
-/

open scoped BigOperators Matrix.Norms.Operator
open Matrix

noncomputable section

namespace PlanarHom.ExponentialDual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The genuine matrix-exponential dual objective. -/
def objective (P C : Matrix V V ℝ) : ℝ :=
  (NormedSpace.exp ℝ C).trace - (C * P).trace

/-- A uniform scalar lower bound, valid for every coefficient in `[μ, M]`. -/
theorem scalar_coercive_bound {μ M p : ℝ} (hp : μ ≤ p) (hpM : p ≤ M) (t : ℝ) :
    μ * |t| - (M + μ) ^ 2 ≤ Real.exp t - p * t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    have hexp := Real.quadratic_le_exp_of_nonneg ht
    have hpt := mul_le_mul_of_nonneg_right hpM ht
    nlinarith [sq_nonneg (t - (M + μ)), sq_nonneg (M + μ)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht']
    have hpt := mul_le_mul_of_nonpos_right hp ht'
    nlinarith [Real.exp_pos t, sq_nonneg (M + μ)]

/-- Every entry of a real unitary matrix has absolute value at most one. -/
theorem abs_unitary_entry_le_one (U : unitary (Matrix V V ℝ)) (i j : V) :
    |(U : Matrix V V ℝ) i j| ≤ 1 := by
  have hs := congrArg (fun A : Matrix V V ℝ => A i i) (unitary.coe_mul_star_self U)
  have hsum : ∑ k, ((U : Matrix V V ℝ) i k) ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, pow_two] using hs
  have hle : ((U : Matrix V V ℝ) i j) ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  exact (sq_le_one_iff_abs_le_one _).mp hle

/-- The sum of absolute eigenvalues controls each matrix entry. -/
theorem abs_entry_le_sum_abs_eigenvalues {C : Matrix V V ℝ} (hC : C.IsHermitian)
    (i j : V) : |C i j| ≤ ∑ k, |hC.eigenvalues k| := by
  have hentry : C i j = ∑ k,
      (hC.eigenvectorUnitary : Matrix V V ℝ) i k * hC.eigenvalues k *
      (hC.eigenvectorUnitary : Matrix V V ℝ) j k := by
    conv_lhs => rw [hC.spectral_theorem]
    simp only [Matrix.mul_apply, Matrix.star_apply, Function.comp_def]
    simp [Matrix.diagonal_apply]
  rw [hentry]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_mul]
  calc
    |(hC.eigenvectorUnitary : Matrix V V ℝ) i k| * |hC.eigenvalues k| *
        |(hC.eigenvectorUnitary : Matrix V V ℝ) j k|
        ≤ 1 * |hC.eigenvalues k| * 1 := by
      gcongr <;> exact abs_unitary_entry_le_one _ _ _
    _ = _ := by ring

/-- The CFC spectral exponential agrees with the genuine convergent power series. -/
theorem trace_exp_eq_sum {C : Matrix V V ℝ} (hC : C.IsHermitian) :
    (NormedSpace.exp ℝ C).trace = ∑ i, Real.exp (hC.eigenvalues i) := by
  rw [← CFC.real_exp_eq_normedSpace_exp hC, hC.cfc_eq,
    Matrix.IsHermitian.cfc, Matrix.trace_mul_cycle]
  simp [Function.comp_def]

/-- The linear term of the dual in an eigenbasis of its variable. -/
theorem trace_mul_eq_sum {C : Matrix V V ℝ} (hC : C.IsHermitian)
    (P : Matrix V V ℝ) :
    (C * P).trace = ∑ i, hC.eigenvalues i *
      (star (hC.eigenvectorUnitary : Matrix V V ℝ) * P *
        (hC.eigenvectorUnitary : Matrix V V ℝ)) i i := by
  conv_lhs => rw [hC.spectral_theorem]
  rw [Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.trace]
  simp [mul_comm]

/-- Conjugation by a real unitary preserves a uniform positive lower bound. -/
theorem rotated_diagonal_bounds {P : Matrix V V ℝ} {μ : ℝ}
    (hP : P.PosSemidef) (hμ : (P - μ • (1 : Matrix V V ℝ)).PosSemidef)
    (U : unitary (Matrix V V ℝ)) (i : V) :
    μ ≤ (star (U : Matrix V V ℝ) * P * U) i i ∧
      (star (U : Matrix V V ℝ) * P * U) i i ≤ P.trace := by
  have hrot := hP.conjTranspose_mul_mul_same (U : Matrix V V ℝ)
  have hrotμ := hμ.conjTranspose_mul_mul_same (U : Matrix V V ℝ)
  have hid : (star (U : Matrix V V ℝ) * (P - μ • (1 : Matrix V V ℝ)) * U) =
      star (U : Matrix V V ℝ) * P * U - μ • (1 : Matrix V V ℝ) := by
    simp [mul_sub, sub_mul, mul_assoc]
  have hl := hrotμ.2 (Pi.single i 1)
  change 0 ≤ star (Pi.single i 1) ⬝ᵥ
    ((star (U : Matrix V V ℝ) * (P - μ • (1 : Matrix V V ℝ)) * (U : Matrix V V ℝ)) *ᵥ _) at hl
  rw [hid] at hl
  simp only [star_trivial, Matrix.mulVec_single_one, single_dotProduct, one_mul,
    Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hl
  refine ⟨by linarith, ?_⟩
  have hn (j : V) : 0 ≤ (star (U : Matrix V V ℝ) * P * U) j j := by
    simpa using hrot.2 (Pi.single j 1)
  have ht : (star (U : Matrix V V ℝ) * P * U).trace = P.trace := by
    rw [Matrix.trace_mul_cycle]
    simp
  rw [← ht, Matrix.trace]
  exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)

/-- A positive-definite matrix dominates a positive scalar multiple of the identity. -/
theorem exists_pos_shift_posSemidef {P : Matrix V V ℝ} (hP : P.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ (P - μ • (1 : Matrix V V ℝ)).PosSemidef := by
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨1, zero_lt_one, ?_⟩
    have hzero : P - (1 : ℝ) • (1 : Matrix V V ℝ) = 0 := Subsingleton.elim _ _
    rw [hzero]
    exact Matrix.PosSemidef.zero
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ hP.1.eigenvalues
    Finset.univ_nonempty
  refine ⟨hP.1.eigenvalues i, hP.eigenvalues_pos i, ?_⟩
  let μ := hP.1.eigenvalues i
  have hd : (Matrix.diagonal (fun j => hP.1.eigenvalues j - μ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (hi j (Finset.mem_univ j)))
  have heq : P - μ • (1 : Matrix V V ℝ) =
      (hP.1.eigenvectorUnitary : Matrix V V ℝ) *
      Matrix.diagonal (fun j => hP.1.eigenvalues j - μ) *
      star (hP.1.eigenvectorUnitary : Matrix V V ℝ) := by
    rw [← Matrix.diagonal_sub, mul_sub, sub_mul]
    have hp := hP.1.spectral_theorem
    simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] at hp
    rw [← hp]
    have hdiag : (Matrix.diagonal (fun (_ : V) => μ)) = μ • (1 : Matrix V V ℝ) := by
      ext j k
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hdiag]
    simp
  rw [heq]
  exact hd.mul_mul_conjTranspose_same _

/-- Quantitative coercivity in the spectral trace norm. -/
theorem objective_ge_eigenvalue_bound {P C : Matrix V V ℝ} {μ : ℝ}
    (hP : P.PosSemidef)
    (hshift : (P - μ • (1 : Matrix V V ℝ)).PosSemidef) (hC : C.IsHermitian) :
    μ * (∑ i, |hC.eigenvalues i|) -
      Fintype.card V * (P.trace + μ) ^ 2 ≤ objective P C := by
  rw [objective, trace_exp_eq_sum hC, trace_mul_eq_sum hC, ← Finset.sum_sub_distrib]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    scalar_coercive_bound
      (rotated_diagonal_bounds hP hshift hC.eigenvectorUnitary i).1
      (rotated_diagonal_bounds hP hshift hC.eigenvectorUnitary i).2
      (hC.eigenvalues i))
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum

/-- Quantitative coercivity controls every matrix entry. -/
theorem objective_ge_entry_bound {P C : Matrix V V ℝ} {μ : ℝ}
    (hP : P.PosSemidef) (hμ : 0 ≤ μ)
    (hshift : (P - μ • (1 : Matrix V V ℝ)).PosSemidef)
    (hC : C.IsHermitian) (i j : V) :
    μ * |C i j| - Fintype.card V * (P.trace + μ) ^ 2 ≤ objective P C := by
  exact (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (abs_entry_le_sum_abs_eigenvalues hC i j) hμ) _).trans
    (objective_ge_eigenvalue_bound hP hshift hC)

/-- Every positive-definite target gives a single coercive bound valid for all
symmetric matrices and all their entries. -/
theorem exists_coercive_entry_bound {P : Matrix V V ℝ} (hP : P.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ b : ℝ, ∀ C : Matrix V V ℝ, C.IsHermitian →
      ∀ i j, μ * |C i j| - b ≤ objective P C := by
  obtain ⟨μ, hμ, hshift⟩ := exists_pos_shift_posSemidef hP
  exact ⟨μ, hμ, Fintype.card V * (P.trace + μ) ^ 2,
    fun C hC i j => objective_ge_entry_bound hP.posSemidef hμ.le hshift hC i j⟩

/-- The true matrix exponential of a real symmetric matrix is positive definite. -/
theorem exp_posDef {C : Matrix V V ℝ} (hC : C.IsHermitian) :
    (NormedSpace.exp ℝ C).PosDef := by
  rw [← CFC.real_exp_eq_normedSpace_exp hC, hC.cfc_eq, Matrix.IsHermitian.cfc]
  apply (Matrix.posDef_diagonal_iff.mpr (by simpa using
    (fun i : V => Real.exp_pos (hC.eigenvalues i)))).mul_mul_conjTranspose_same
  rw [Matrix.vecMul_injective_iff_isUnit, ← unitary.val_toUnits_apply]
  exact Units.isUnit _

/-- The spectral logarithm of the genuine symmetric exponential recovers its input. -/
theorem matrixLog_exp {C : Matrix V V ℝ} (hC : C.IsHermitian) :
    EntropyCompletion.matrixLog (NormedSpace.exp ℝ C) = C := by
  exact CFC.log_exp C hC

/-- Continuity of the genuine exponential dual on all matrices. -/
theorem continuous_objective (P : Matrix V V ℝ) : Continuous (objective P) := by
  exact NormedSpace.exp_continuous.matrix_trace.sub
    (continuous_id.matrix_mul continuous_const).matrix_trace

/-- Every symmetric sublevel set is compact for every fixed positive-definite P. -/
theorem isCompact_sublevel {P : Matrix V V ℝ} (hP : P.PosDef) (r : ℝ) :
    IsCompact {C : Matrix V V ℝ | C.IsHermitian ∧ objective P C ≤ r} := by
  obtain ⟨μ, hμ, hshift⟩ := exists_pos_shift_posSemidef hP
  let R : ℝ := (r + Fintype.card V * (P.trace + μ) ^ 2) / μ
  have hc : IsClosed {C : Matrix V V ℝ | C.IsHermitian ∧ objective P C ≤ r} := by
    apply IsClosed.inter
    · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
    · exact isClosed_le (continuous_objective P) continuous_const
  apply (isCompact_Icc (a := (fun (_ _ : V) => -R))
    (b := (fun (_ _ : V) => R))).of_isClosed_subset hc
  intro C hC
  have hbound (i j : V) : |C i j| ≤ R := by
    apply (le_div_iff₀ hμ).mpr
    have hb := objective_ge_entry_bound hP.posSemidef hμ.le hshift hC.1 i j
    nlinarith [hC.2]
  exact ⟨fun i j => (abs_le.mp (hbound i j)).1,
    fun i j => (abs_le.mp (hbound i j)).2⟩

/-- Any nonempty closed set of symmetric matrices admits a dual minimizer.
In particular this applies to every closed symmetric support subspace. -/
theorem exists_minimizer {P : Matrix V V ℝ} (hP : P.PosDef)
    (S : Set (Matrix V V ℝ)) (hclosed : IsClosed S) (hne : S.Nonempty)
    (hsymm : ∀ C ∈ S, C.IsHermitian) :
    ∃ C ∈ S, ∀ D ∈ S, objective P C ≤ objective P D := by
  obtain ⟨C₀, hC₀⟩ := hne
  let T := S ∩ {C : Matrix V V ℝ | C.IsHermitian ∧ objective P C ≤ objective P C₀}
  have hcompact : IsCompact T :=
    (isCompact_sublevel hP (objective P C₀)).inter_left hclosed
  have hT : T.Nonempty := ⟨C₀, hC₀, hsymm C₀ hC₀, le_rfl⟩
  obtain ⟨C, hC, hmin⟩ := hcompact.exists_isMinOn hT (continuous_objective P).continuousOn
  refine ⟨C, hC.1, fun D hD => ?_⟩
  by_cases hle : objective P D ≤ objective P C₀
  · exact hmin ⟨hD, hsymm D hD, hle⟩
  · exact hC.2.2.trans (le_of_not_ge hle)

/-- The exponential dual attains its minimum on every symmetric linear support
subspace. Finite dimensionality supplies closedness automatically. -/
theorem exists_minimizer_submodule {P : Matrix V V ℝ} (hP : P.PosDef)
    (S : Submodule ℝ (Matrix V V ℝ)) (hsymm : ∀ C ∈ S, C.IsHermitian) :
    ∃ C ∈ S, ∀ D ∈ S, objective P C ≤ objective P D := by
  exact exists_minimizer hP S S.closed_of_finiteDimensional ⟨0, S.zero_mem⟩ hsymm

/-- The explicit positive-definite equicorrelation point gives an unconditional
minimizer for the graph-completion dual whenever `0 ≤ x < 1`. -/
theorem exists_equicorrelation_minimizer {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (S : Submodule ℝ (Matrix V V ℝ)) (hsymm : ∀ C ∈ S, C.IsHermitian) :
    ∃ C ∈ S, ∀ D ∈ S,
      objective (EntropyCompletion.equicorrelation x) C ≤
      objective (EntropyCompletion.equicorrelation x) D := by
  exact exists_minimizer_submodule (EntropyCompletion.equicorrelation_posDef hx hx1) S hsymm

end PlanarHom.ExponentialDual

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Analytic.Constructions

/-!
# The feasible matrix slice for entropy completion

This file proves the analytic setup for Lemma 4.5 on the actual graph-distance
kernel and the actual spectral entropy objective:

* the feasible PSD slice is nonempty, convex, closed, and compact;
* `(1 - x) I + x J` is a PD feasible point for `0 ≤ x < 1`;
* the connected graph-distance kernel is PD in a neighborhood of zero;
* the CFC entropy objective has the specified eigenvalue formula, is continuous
  on the feasible slice, and attains its minimum there.

The minimizer's interiority, the matrix entropy differential/Hessian formulas,
and the analytic-continuation step are not claimed here. In particular, this
file does not state Lemma 4.5 with extra optimizer or continuation hypotheses.
-/

open scoped BigOperators ComplexOrder
open Matrix

noncomputable section

namespace PlanarHom
namespace EntropyCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The PSD correlation matrices with value `x` at every edge. -/
def feasibleSet (G : SimpleGraph V) (x : ℝ) : Set (Matrix V V ℝ) :=
  {H | H.PosSemidef ∧ (∀ i, H i i = 1) ∧ ∀ i j, G.Adj i j → H i j = x}

/-- A strictly feasible matrix whenever `0 ≤ x < 1`. -/
def equicorrelation (x : ℝ) : Matrix V V ℝ :=
  (1 - x) • (1 : Matrix V V ℝ) + x • Matrix.of (fun _ _ => 1)

omit [Fintype V] in
@[simp] theorem equicorrelation_diag (x : ℝ) (i : V) :
    equicorrelation x i i = 1 := by
  simp [equicorrelation, Matrix.add_apply, Matrix.smul_apply]

omit [Fintype V] in
theorem equicorrelation_offDiag (x : ℝ) {i j : V} (hij : i ≠ j) :
    equicorrelation x i j = x := by
  simp [equicorrelation, Matrix.add_apply, Matrix.smul_apply, hij]

theorem equicorrelation_posDef {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    (equicorrelation (V := V) x).PosDef := by
  apply (Matrix.PosDef.one.smul (sub_pos.mpr hx1)).add_posSemidef
  have hJ : (Matrix.of (fun (_ _ : V) => (1 : ℝ))).PosSemidef := by
    simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun (_ : V) => (1 : ℝ))
  exact hJ.smul hx

theorem equicorrelation_mem_feasibleSet (G : SimpleGraph V) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) : equicorrelation x ∈ feasibleSet G x := by
  refine ⟨(equicorrelation_posDef hx hx1).posSemidef, equicorrelation_diag x, ?_⟩
  intro i j hij
  exact equicorrelation_offDiag x hij.ne

theorem feasibleSet_nonempty (G : SimpleGraph V) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) : (feasibleSet G x).Nonempty :=
  ⟨equicorrelation x, equicorrelation_mem_feasibleSet G hx hx1⟩

omit [DecidableEq V] in
theorem convex_feasibleSet (G : SimpleGraph V) (x : ℝ) :
    Convex ℝ (feasibleSet G x) := by
  intro A hA B hB a b ha hb hab
  refine ⟨(hA.1.smul ha).add (hB.1.smul hb), ?_, ?_⟩
  · intro i
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      hA.2.1 i, hB.2.1 i, mul_one] using hab
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      hA.2.2 i j hij, hB.2.2 i j hij, ← add_mul, hab, one_mul]

omit [DecidableEq V] in
theorem isClosed_posSemidef : IsClosed {H : Matrix V V ℝ | H.PosSemidef} := by
  change IsClosed ({H : Matrix V V ℝ | H.IsHermitian} ∩
    {H : Matrix V V ℝ | ∀ v, 0 ≤ star v ⬝ᵥ (H *ᵥ v)})
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

omit [DecidableEq V] in
theorem isClosed_feasibleSet (G : SimpleGraph V) (x : ℝ) :
    IsClosed (feasibleSet G x) := by
  change IsClosed ({H : Matrix V V ℝ | H.PosSemidef} ∩
    ({H : Matrix V V ℝ | ∀ i, H i i = 1} ∩
      {H : Matrix V V ℝ | ∀ i j, G.Adj i j → H i j = x}))
  apply isClosed_posSemidef.inter
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
      (fun (_ : G.Adj i j) => isClosed_eq (continuous_id.matrix_elem i j) continuous_const)))

/-- The two-vector tests `eᵢ ± eⱼ` bound every entry of a PSD matrix with
unit diagonal. This is the boundedness argument in Lemma 4.5. -/
theorem entry_bounds_of_posSemidef_unitDiag {H : Matrix V V ℝ}
    (hH : H.PosSemidef) (hd : ∀ i, H i i = 1) (i j : V) :
    -1 ≤ H i j ∧ H i j ≤ 1 := by
  have hs : H j i = H i j := by
    have h := congrArg (fun M : Matrix V V ℝ => M i j) hH.1
    simpa using h
  have hplus := hH.2 (Pi.single i 1 + Pi.single j 1)
  have hminus := hH.2 (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
    hd i, hd j, hs] at hplus hminus
  constructor <;> linarith

theorem isCompact_feasibleSet (G : SimpleGraph V) (x : ℝ) :
    IsCompact (feasibleSet G x) := by
  apply (isCompact_Icc (a := (fun (_ _ : V) => (-1 : ℝ)))
    (b := (fun (_ _ : V) => (1 : ℝ)))).of_isClosed_subset (isClosed_feasibleSet G x)
  intro H hH
  constructor
  · intro i j
    exact (entry_bounds_of_posSemidef_unitDiag hH.1 hH.2.1 i j).1
  · intro i j
    exact (entry_bounds_of_posSemidef_unitDiag hH.1 hH.2.1 i j).2

/-- The graph-distance kernel in Lemma 4.5. -/
def distanceKernel (G : SimpleGraph V) (x : ℝ) : Matrix V V ℝ :=
  Matrix.of (fun i j => x ^ G.dist i j)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem distanceKernel_diag (G : SimpleGraph V) (x : ℝ) (i : V) :
    distanceKernel G x i i = 1 := by simp [distanceKernel, G.dist_self]

omit [Fintype V] [DecidableEq V] in
theorem distanceKernel_edge (G : SimpleGraph V) (x : ℝ) {i j : V}
    (hij : G.Adj i j) : distanceKernel G x i j = x := by
  simp [distanceKernel, G.dist_eq_one_iff_adj.mpr hij]

omit [Fintype V] [DecidableEq V] in
theorem distanceKernel_isHermitian (G : SimpleGraph V) (x : ℝ) :
    (distanceKernel G x).IsHermitian := by
  ext i j
  simp [distanceKernel, Matrix.conjTranspose_apply, G.dist_comm]

omit [Fintype V] in
theorem distanceKernel_zero (G : SimpleGraph V) (hG : G.Connected) :
    distanceKernel G 0 = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [distanceKernel, hij,
      show G.dist i j ≠ 0 from fun h => hij (hG.dist_eq_zero_iff.mp h)]

omit [Fintype V] [DecidableEq V] in
theorem continuous_distanceKernel (G : SimpleGraph V) :
    Continuous (distanceKernel G) := by
  apply continuous_matrix
  intro i j
  exact continuous_id.pow _

omit [Fintype V] [DecidableEq V] in
/-- Each entry of the graph-distance kernel is a polynomial in the parameter. -/
theorem analyticAt_distanceKernel_entry (G : SimpleGraph V) (x : ℝ) (i j : V) :
    AnalyticAt ℝ (fun t : ℝ => distanceKernel G t i j) x :=
  analyticAt_id.pow _

omit [DecidableEq V] in
theorem distanceKernel_mem_feasibleSet (G : SimpleGraph V) {x : ℝ}
    (h : (distanceKernel G x).PosSemidef) : distanceKernel G x ∈ feasibleSet G x :=
  ⟨h, distanceKernel_diag G x, fun _ _ hij => distanceKernel_edge G x hij⟩

omit [DecidableEq V] in
/-- Every feasible matrix has the same trace. -/
theorem trace_eq_card_of_mem_feasibleSet (G : SimpleGraph V) {x : ℝ}
    {H : Matrix V V ℝ} (hH : H ∈ feasibleSet G x) :
    H.trace = Fintype.card V := by
  simp [Matrix.trace, hH.2.1]

/-- PSD and fixed trace give a common compact interval containing the spectra. -/
theorem spectrum_subset_of_mem_feasibleSet (G : SimpleGraph V) {x : ℝ}
    {H : Matrix V V ℝ} (hH : H ∈ feasibleSet G x) :
    spectrum ℝ H ⊆ Set.Icc 0 (Fintype.card V : ℝ) := by
  rw [hH.1.1.spectrum_real_eq_range_eigenvalues]
  rintro t ⟨i, rfl⟩
  refine ⟨hH.1.eigenvalues_nonneg i, ?_⟩
  calc
    hH.1.1.eigenvalues i ≤ ∑ j, hH.1.1.eigenvalues j :=
      Finset.single_le_sum (fun j _ => hH.1.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = H.trace := by simpa using hH.1.1.trace_eq_sum_eigenvalues.symm
    _ = Fintype.card V := trace_eq_card_of_mem_feasibleSet G hH

/-- A real Hermitian matrix with diagonal one and off-diagonal row sums
strictly less than one is positive definite, by Gershgorin. -/
theorem posDef_of_unitDiag_rowSum_lt_one {H : Matrix V V ℝ}
    (hH : H.IsHermitian) (hd : ∀ i, H i i = 1)
    (hs : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖H i j‖ < 1) : H.PosDef := by
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
  have hk' : |hH.eigenvalues i - 1| < 1 := by
    apply lt_of_le_of_lt _ (hs k)
    simpa [Metric.mem_closedBall, Real.dist_eq, hd k] using hk
  have := (abs_lt.mp hk').1
  linarith

/-- The graph-distance kernel is PD in a neighborhood of zero.
This is stronger than the one-sided initial-PD fact used in Lemma 4.5. -/
theorem eventually_posDef_distanceKernel (G : SimpleGraph V) (hG : G.Connected) :
    ∀ᶠ x : ℝ in nhds 0, (distanceKernel G x).PosDef := by
  have hc (i : V) : Continuous (fun x : ℝ =>
      ∑ j ∈ Finset.univ.erase i, ‖distanceKernel G x i j‖) := by
    exact continuous_finset_sum _ (fun j _ =>
      ((continuous_distanceKernel G).matrix_elem i j).norm)
  have hzero (i : V) : (∑ j ∈ Finset.univ.erase i,
      ‖distanceKernel G 0 i j‖) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [distanceKernel_zero G hG, Ne.symm hji]
  have he (i : V) : ∀ᶠ x : ℝ in nhds 0,
      ∑ j ∈ Finset.univ.erase i, ‖distanceKernel G x i j‖ < 1 :=
    (hc i).continuousAt.eventually (gt_mem_nhds (by rw [hzero i]; norm_num :
      (∑ j ∈ Finset.univ.erase i, ‖distanceKernel G 0 i j‖) < (1 : ℝ)))
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  exact posDef_of_unitDiag_rowSum_lt_one (distanceKernel_isHermitian G x)
    (distanceKernel_diag G x) hx

/-- The entropy objective, with the standard value `0 log 0 = 0` on the
singular boundary, defined by real continuous functional calculus. -/
def entropyObjective (H : Matrix V V ℝ) : ℝ :=
  (cfc (fun t : ℝ => t * Real.log t - t) H).trace

/-- The objective is literally the sum of `λ log λ − λ` over eigenvalues. -/
theorem entropyObjective_eq_sum {H : Matrix V V ℝ} (hH : H.IsHermitian) :
    entropyObjective H = ∑ i,
      (hH.eigenvalues i * Real.log (hH.eigenvalues i) - hH.eigenvalues i) := by
  rw [entropyObjective, hH.cfc_eq, Matrix.IsHermitian.cfc, Matrix.trace_mul_cycle]
  simp [Function.comp_def]


/-- Real matrices embedded entrywise into complex matrices. The real
star-algebra structure lets us use the complex isometric CFC continuity API. -/
private def complexify : Matrix V V ℝ →⋆ₐ[ℝ] Matrix V V ℂ :=
  { (Algebra.ofId ℝ ℂ).mapMatrix with
    map_star' := by intro H; ext i j; simp }

private theorem complexify_apply (H : Matrix V V ℝ) :
    complexify H = H.map (fun t : ℝ => (t : ℂ)) := rfl

private theorem continuous_complexify :
    Continuous (complexify : Matrix V V ℝ → Matrix V V ℂ) := by
  apply continuous_matrix
  intro i j
  exact Complex.continuous_ofReal.comp (continuous_id.matrix_elem i j)

private theorem complexify_isHermitian {H : Matrix V V ℝ} (hH : H.IsHermitian) :
    (complexify H).IsHermitian := by
  rw [complexify_apply]
  exact hH.map _ (fun t => by simp)

private theorem real_cfc_eq_complex_cfc_trace {H : Matrix V V ℝ}
    (hH : H.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f H).trace = (cfc f (complexify H)).trace.re := by
  have hm : complexify (cfc f H) = cfc f (complexify H) :=
    complexify.map_cfc f H hf.continuousOn continuous_complexify hH
      (complexify_isHermitian hH)
  rw [← hm, complexify_apply]
  simp [Matrix.trace, Matrix.map_apply]

open scoped Matrix.Norms.L2Operator in
theorem continuousOn_entropyObjective (G : SimpleGraph V) (x : ℝ) :
    ContinuousOn entropyObjective (feasibleSet G x) := by
  letI : CStarAlgebra (Matrix V V ℂ) := {}
  have hc : ContinuousOn
      (fun H : Matrix V V ℝ => cfc (fun t : ℝ => t * Real.log t - t) (complexify H))
      (feasibleSet G x) := by
    apply ContinuousOn.cfc (s := Set.Icc 0 (Fintype.card V : ℝ)) isCompact_Icc
      (fun t : ℝ => t * Real.log t - t) continuous_complexify.continuousOn
    · intro H hH
      exact (AlgHom.spectrum_apply_subset complexify.toAlgHom H).trans
        (spectrum_subset_of_mem_feasibleSet G hH)
    · intro H hH
      exact complexify_isHermitian hH.1.1
  have ht : ContinuousOn (fun H : Matrix V V ℝ =>
      (cfc (fun t : ℝ => t * Real.log t - t) (complexify H)).trace.re)
      (feasibleSet G x) :=
    Complex.continuous_re.continuousOn.comp
      (continuous_id.matrix_trace.continuousOn.comp hc (fun _ _ => Set.mem_univ _))
      (fun _ _ => Set.mem_univ _)
  apply ht.congr
  intro H hH
  exact real_cfc_eq_complex_cfc_trace hH.1.1 _ (Real.continuous_mul_log.sub continuous_id)

/-- The actual entropy minimization problem has a minimizer for every
`0 ≤ x < 1`. Positive definiteness of that minimizer is a separate step. -/
theorem exists_entropy_minimizer (G : SimpleGraph V) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ H ∈ feasibleSet G x, ∀ K ∈ feasibleSet G x,
      entropyObjective H ≤ entropyObjective K := by
  exact (isCompact_feasibleSet G x).exists_isMinOn
    (feasibleSet_nonempty G hx hx1) (continuousOn_entropyObjective G x)

/-- Every feasible PSD matrix can be regularized toward the explicit PD
feasible point without changing its diagonal or constrained edge entries. -/
theorem regularized_feasible_posDef (G : SimpleGraph V) {x ε : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {H : Matrix V V ℝ} (hH : H ∈ feasibleSet G x) :
    ((1 - ε) • H + ε • equicorrelation x) ∈ feasibleSet G x ∧
      ((1 - ε) • H + ε • equicorrelation x).PosDef := by
  constructor
  · exact convex_feasibleSet G x hH (equicorrelation_mem_feasibleSet G hx hx1)
      (sub_nonneg.mpr hε1) hε.le (by ring)
  · exact Matrix.PosDef.posSemidef_add (hH.1.smul (sub_nonneg.mpr hε1))
      ((equicorrelation_posDef hx hx1).smul hε)

/-- The genuine spectral matrix logarithm, including its totalized boundary
convention. In the PD region it is the ordinary matrix logarithm. -/
def matrixLog (H : Matrix V V ℝ) : Matrix V V ℝ := cfc Real.log H

/-- The exact sparsity condition used in Lemma 4.5, with no PD conclusion
folded into its hypothesis. -/
def logVanishesOnNonedges (G : SimpleGraph V) (H : Matrix V V ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬G.Adj i j → matrixLog H i j = 0

/-- The original small-positive-parameter hypothesis of Lemma 4.5. -/
def initiallyLogSparse (G : SimpleGraph V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
    logVanishesOnNonedges G (distanceKernel G x)

/-
Remaining dependencies for Lemma 4.5, not assumptions of any theorem above:

1. For `0 < x < 1`, every entropy minimizer furnished above is PD.
   One route is the paper's singular-eigenvalue perturbation estimate along
   `regularized_feasible_posDef`; this requires quantitative spectral analysis.
2. On the PD cone, the derivative of `entropyObjective` is the Frobenius
   pairing with `matrixLog`, and the Hessian is positive on nonzero symmetric
   directions. These imply uniqueness and the nonedge first-order condition.
3. For the symmetric support subspace, the projected matrix exponential has
   invertible differential everywhere. Its local analytic inverse then gives
   an analytic optimizer curve. Mathlib already supplies the analytic inverse
   theorem; the missing part is its matrix-specific derivative/invertibility
   input, not an absent abstract analytic inverse theorem.
4. Identify the initially PD distance kernel with that optimizer and apply the
   real analytic identity theorem on `(0, 1)` entrywise.

A dual exponential minimization route can avoid dependency 1, but would still
need proved coercivity, trace-exponential derivatives, and positive Hessian.
-/

end EntropyCompletion
end PlanarHom

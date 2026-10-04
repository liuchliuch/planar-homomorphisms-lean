import Mathlib.Analysis.Matrix.Order
import PlanarHom.AnalyticInverse
import PlanarHom.ExponentialDual
import PlanarHom.ExponentialGradient
import PlanarHom.TraceExponential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Positive-definite continuation of logarithmically sparse distance kernels

This is the exponential-dual proof of Lemma 4.5. Minimizing the genuine dual
on the graph support subspace gives a supported-gradient preimage of every
strictly feasible equicorrelation target. The positive Hessian supplies an
analytic inverse. The resulting exponential curve is positive definite and
agrees initially with the distance kernel; the analytic identity principle
propagates that agreement to the whole interval `(0, 1)`.

Neither optimizer existence, optimizer interiority, nor analytic continuation
is assumed in the final theorem.
-/

open scoped BigOperators Matrix.Norms.Operator
open Matrix

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace PlanarHom.KernelContinuation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Symmetric matrices supported on the diagonal and the edges of a graph. -/
def supportSpace (G : SimpleGraph V) : Submodule ℝ (Matrix V V ℝ) where
  carrier := {C | C.IsHermitian ∧ ∀ i j, i ≠ j → ¬G.Adj i j → C i j = 0}
  zero_mem' := ⟨Matrix.isHermitian_zero, by simp⟩
  add_mem' := by
    rintro A B ⟨hA, hAs⟩ ⟨hB, hBs⟩
    exact ⟨hA.add hB, by intros; simp [*]⟩
  smul_mem' := by
    rintro r C ⟨hC, hCs⟩
    refine ⟨?_, by intros; simp [*]⟩
    change (r • C)ᴴ = r • C
    rw [Matrix.conjTranspose_smul, hC]
    simp

omit [Fintype V] [DecidableEq V] in
theorem supportSpace_hermitian (G : SimpleGraph V) (C : supportSpace G) :
    (C : Matrix V V ℝ).IsHermitian := C.property.1

/-- Restriction of trace pairing to the supported symmetric subspace. -/
def supportedPairing (G : SimpleGraph V) :
    Matrix V V ℝ →L[ℝ] (supportSpace G →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => (TraceExponential.tracePairing P).comp (supportSpace G).subtypeL
      map_add' := by intro A B; ext D; simp
      map_smul' := by intro r A; ext D; simp }

omit [DecidableEq V] in
@[simp] theorem supportedPairing_apply (G : SimpleGraph V)
    (P : Matrix V V ℝ) (D : supportSpace G) :
    supportedPairing G P D = (P * (D : Matrix V V ℝ)).trace := rfl

/-- The gradient of the exponential dual on the graph support space. -/
def gradient (G : SimpleGraph V) (C : supportSpace G) : supportSpace G →L[ℝ] ℝ :=
  supportedPairing G (NormedSpace.exp ℝ (C : Matrix V V ℝ))

/-- First-order optimality in every supported symmetric direction. -/
theorem gradient_eq_of_minimizer (G : SimpleGraph V) (P : Matrix V V ℝ)
    (C : supportSpace G)
    (hmin : ∀ D : supportSpace G,
      ExponentialDual.objective P C ≤ ExponentialDual.objective P D) :
    gradient G C = supportedPairing G P := by
  have hlocal : IsLocalMin
      (fun D : supportSpace G => ExponentialDual.objective P D) C :=
    Filter.Eventually.of_forall hmin
  have htrace := (TraceExponential.hasFDerivAt_trace_exp (C : Matrix V V ℝ)).comp C
    (supportSpace G).subtypeL.hasFDerivAt
  have hlin : HasFDerivAt (fun D : supportSpace G => ((D : Matrix V V ℝ) * P).trace)
      (supportedPairing G P) C := by
    convert (supportedPairing G P).hasFDerivAt (x := C) using 1
    funext D
    exact Matrix.trace_mul_comm (D : Matrix V V ℝ) P
  have hzero := hlocal.hasFDerivAt_eq_zero (htrace.sub hlin)
  change gradient G C - supportedPairing G P = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- Every positive-definite target is attained by the supported exponential gradient. -/
theorem exists_gradient_eq (G : SimpleGraph V) {P : Matrix V V ℝ} (hP : P.PosDef) :
    ∃ C : supportSpace G, gradient G C = supportedPairing G P := by
  obtain ⟨C, hC, hmin⟩ := ExponentialDual.exists_minimizer_submodule hP (supportSpace G)
    (fun _ h => h.1)
  exact ⟨⟨C, hC⟩, gradient_eq_of_minimizer G P ⟨C, hC⟩ (fun D => hmin D D.property)⟩

/-- Supported trace pairings only depend on the diagonal and edge entries. -/
theorem supportedPairing_eq_of_entries (G : SimpleGraph V) {H P : Matrix V V ℝ}
    (hd : ∀ i, H i i = P i i)
    (he : ∀ i j, G.Adj i j → H i j = P i j) :
    supportedPairing G H = supportedPairing G P := by
  ext D
  simp only [supportedPairing_apply, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change H i j * (D : Matrix V V ℝ) j i = P i j * (D : Matrix V V ℝ) j i
  by_cases hij : i = j
  · subst j; rw [hd]
  by_cases hadj : G.Adj i j
  · rw [he i j hadj]
  · have hzero := D.property.2 j i (Ne.symm hij) (by simpa [G.adj_comm] using hadj)
    rw [hzero]; simp

open scoped MatrixOrder in
/-- A positive-definite matrix is recovered from its genuine spectral logarithm. -/
theorem exp_matrixLog {H : Matrix V V ℝ} (hH : H.PosDef) :
    NormedSpace.exp ℝ (EntropyCompletion.matrixLog H) = H := by
  apply CFC.exp_log H ?_
  apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) H hH.1).mpr
  rw [hH.1.spectrum_real_eq_range_eigenvalues]
  rintro t ⟨i, rfl⟩
  exact hH.eigenvalues_pos i

/-- Under the paper's nonedge condition, the logarithm lies in the support space. -/
theorem matrixLog_mem_supportSpace (G : SimpleGraph V) {H : Matrix V V ℝ}
    (hs : EntropyCompletion.logVanishesOnNonedges G H) :
    EntropyCompletion.matrixLog H ∈ supportSpace G :=
  ⟨IsSelfAdjoint.log, hs⟩

/-- A positive-definite, logarithmically sparse distance kernel solves the dual
first-order equation. -/
theorem gradient_matrixLog_distanceKernel (G : SimpleGraph V) {x : ℝ}
    (hH : (EntropyCompletion.distanceKernel G x).PosDef)
    (hs : EntropyCompletion.logVanishesOnNonedges G (EntropyCompletion.distanceKernel G x)) :
    gradient G ⟨EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G x),
      matrixLog_mem_supportSpace G hs⟩ = supportedPairing G (EntropyCompletion.equicorrelation x) := by
  change supportedPairing G (NormedSpace.exp ℝ
    (EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G x))) = _
  rw [exp_matrixLog hH]
  apply supportedPairing_eq_of_entries
  · intro i; simp
  · intro i j hij
    rw [EntropyCompletion.distanceKernel_edge G x hij,
      EntropyCompletion.equicorrelation_offDiag x hij.ne]

omit [Fintype V] [DecidableEq V] in
/-- The entrywise real-analytic identity principle used at the final continuation step. -/
theorem distanceKernel_eq_of_analytic (G : SimpleGraph V) (H : ℝ → Matrix V V ℝ)
    (ha : ∀ i j, AnalyticOnNhd ℝ (fun x => H x i j) (Set.Ioo 0 1))
    (he : ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < x → x < ε → EntropyCompletion.distanceKernel G x = H x)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : EntropyCompletion.distanceKernel G x = H x := by
  obtain ⟨ε, hε, he⟩ := he
  let z : ℝ := min ε 1 / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have hze : z < ε := by dsimp [z]; have := min_le_left ε 1; linarith [lt_min hε zero_lt_one]
  have hz1 : z < 1 := by dsimp [z]; have := min_le_right ε 1; linarith [lt_min hε zero_lt_one]
  have hnear : EntropyCompletion.distanceKernel G =ᶠ[nhds z] H := by
    filter_upwards [Ioo_mem_nhds hz hze] with t ht
    exact he t ht.1 ht.2
  ext i j
  have hid := (show AnalyticOnNhd ℝ
      (fun t => EntropyCompletion.distanceKernel G t i j) (Set.Ioo 0 1) from
      fun t _ => EntropyCompletion.analyticAt_distanceKernel_entry G t i j)
    |>.eqOn_of_preconnected_of_eventuallyEq (ha i j) isPreconnected_Ioo ⟨hz, hz1⟩
      (hnear.mono (fun t ht => congrArg (fun M : Matrix V V ℝ => M i j) ht))
  exact hid ⟨hx, hx1⟩

/-- The unique exponential completion, expressed using the global inverse of the dual gradient. -/
def completion (G : SimpleGraph V) (x : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp ℝ ((Function.invFun (gradient G)
    (supportedPairing G (EntropyCompletion.equicorrelation x)) : supportSpace G) : Matrix V V ℝ)

/-- The completion is positive definite independently of the value of the parameter. -/
theorem completion_posDef (G : SimpleGraph V) (x : ℝ) : (completion G x).PosDef :=
  ExponentialDual.exp_posDef (supportSpace_hermitian G _)

/-- Equicorrelation is an affine, hence analytic, matrix curve. -/
theorem analyticAt_equicorrelation (x : ℝ) :
    AnalyticAt ℝ (EntropyCompletion.equicorrelation (V := V)) x := by
  exact ((analyticAt_const.sub analyticAt_id).smul analyticAt_const).add
    (analyticAt_id.smul analyticAt_const)

/-- Analyticity of the completion follows from a genuine invertible gradient derivative. -/
theorem analyticAt_completion_of_gradient (G : SimpleGraph V)
    (hinj : Function.Injective (gradient G))
    (ha : ∀ C, AnalyticAt ℝ (gradient G) C)
    (hd : ∀ C, Function.Bijective (fderiv ℝ (gradient G) C))
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : AnalyticAt ℝ (completion G) x := by
  have hp : AnalyticAt ℝ (supportedPairing G) (EntropyCompletion.equicorrelation x) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Matrix V V ℝ)
      (F := supportSpace G →L[ℝ] ℝ) (supportedPairing G) _
  have ht : AnalyticAt ℝ
      (fun t => supportedPairing G (EntropyCompletion.equicorrelation t)) x :=
    hp.comp (analyticAt_equicorrelation (V := V) x)
  have hm : supportedPairing G (EntropyCompletion.equicorrelation x) ∈ Set.range (gradient G) :=
    exists_gradient_eq G (EntropyCompletion.equicorrelation_posDef hx.le hx1)
  have hi := AnalyticInverse.analyticAt_invFun_comp hinj ha hd ht hm
  exact (NormedSpace.exp_analytic _).comp (((supportSpace G).subtypeL.analyticAt _).comp hi)

/-- Entry evaluation as a continuous linear map, independent of the chosen matrix norm. -/
def entryCLM (i j : V) : Matrix V V ℝ →L[ℝ] ℝ where
  toFun := fun M => M i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := continuous_id.matrix_elem i j

/-- Initial sparse distance kernels agree with the unique dual-gradient completion. -/
theorem distanceKernel_eq_completion_of_logSparse (G : SimpleGraph V)
    (hinj : Function.Injective (gradient G)) {x : ℝ}
    (hH : (EntropyCompletion.distanceKernel G x).PosDef)
    (hs : EntropyCompletion.logVanishesOnNonedges G (EntropyCompletion.distanceKernel G x)) :
    EntropyCompletion.distanceKernel G x = completion G x := by
  unfold completion
  rw [← gradient_matrixLog_distanceKernel G hH hs,
    Function.leftInverse_invFun hinj]
  exact (exp_matrixLog hH).symm

/-- Initial positivity and initial log sparsity identify the two curves on a nonempty interval. -/
theorem initially_eq_completion (G : SimpleGraph V) (hG : G.Connected)
    (hinj : Function.Injective (gradient G)) (hs : EntropyCompletion.initiallyLogSparse G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < x → x < ε →
      EntropyCompletion.distanceKernel G x = completion G x := by
  obtain ⟨ε, hε, hs⟩ := hs
  obtain ⟨δ, hδ, hpd⟩ := Metric.eventually_nhds_iff.mp
    (EntropyCompletion.eventually_posDef_distanceKernel G hG)
  refine ⟨min ε δ, lt_min hε hδ, fun x hx hxe => ?_⟩
  apply distanceKernel_eq_completion_of_logSparse G hinj
  · apply hpd
    simpa [Real.dist_eq, abs_of_pos hx] using (lt_min_iff.mp hxe).2
  · exact hs x hx (lt_min_iff.mp hxe).1

/-- The continuation argument, with its matrix-gradient hypotheses isolated for reuse. -/
theorem posDef_distanceKernel_of_gradient (G : SimpleGraph V) (hG : G.Connected)
    (hinj : Function.Injective (gradient G))
    (ha : ∀ C, AnalyticAt ℝ (gradient G) C)
    (hd : ∀ C, Function.Bijective (fderiv ℝ (gradient G) C))
    (hs : EntropyCompletion.initiallyLogSparse G) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (EntropyCompletion.distanceKernel G x).PosDef := by
  have he := distanceKernel_eq_of_analytic G (completion G)
    (fun i j t ht => ((entryCLM i j).analyticAt _).comp
      (analyticAt_completion_of_gradient G hinj ha hd ht.1 ht.2))
    (initially_eq_completion G hG hinj hs) hx hx1
  rw [he]
  exact completion_posDef G x

/-- The completion’s logarithm vanishes on every nonedge. -/
theorem completion_logVanishesOnNonedges (G : SimpleGraph V) (x : ℝ) :
    EntropyCompletion.logVanishesOnNonedges G (completion G x) := by
  intro i j hij hadj
  unfold completion
  rw [ExponentialDual.matrixLog_exp (supportSpace_hermitian G _)]
  exact (Function.invFun (gradient G)
    (supportedPairing G (EntropyCompletion.equicorrelation x))).property.2 i j hij hadj

/-- The graph-specific gradient is the general supported exponential gradient. -/
theorem gradient_eq_exponentialGradient (G : SimpleGraph V) :
    gradient G = ExponentialGradient.gradient (supportSpace G) := rfl

/-- The analytic dual completion agrees with the original distance kernel throughout `(0, 1)`. -/
theorem distanceKernel_eq_completion (G : SimpleGraph V) (hG : G.Connected)
    (hs : EntropyCompletion.initiallyLogSparse G) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    EntropyCompletion.distanceKernel G x = completion G x := by
  have hinj : Function.Injective (gradient G) :=
    ExponentialGradient.gradient_injective (supportSpace G) (fun _ h => h.1)
  have ha : ∀ C, AnalyticAt ℝ (gradient G) C :=
    ExponentialGradient.analyticAt_gradient (supportSpace G)
  have hd : ∀ C, Function.Bijective (fderiv ℝ (gradient G) C) :=
    ExponentialGradient.fderiv_gradient_bijective (supportSpace G) (fun _ h => h.1)
  exact distanceKernel_eq_of_analytic G (completion G)
    (fun i j t ht => ((entryCLM i j).analyticAt _).comp
      (analyticAt_completion_of_gradient G hinj ha hd ht.1 ht.2))
    (initially_eq_completion G hG hinj hs) hx hx1

/-- **Lemma 4.5.** For a finite connected graph whose distance kernel has a
logarithm vanishing on nonedges at every sufficiently small positive parameter,
the distance kernel is positive definite for every parameter strictly between
zero and one. No optimization or continuation hypothesis is added. -/
theorem posDef_distanceKernel (G : SimpleGraph V) (hG : G.Connected)
    (hs : EntropyCompletion.initiallyLogSparse G) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (EntropyCompletion.distanceKernel G x).PosDef := by
  rw [distanceKernel_eq_completion G hG hs hx hx1]
  exact completion_posDef G x

/-- The same continuation also propagates the original logarithmic sparsity. -/
theorem logVanishesOnNonedges_distanceKernel (G : SimpleGraph V) (hG : G.Connected)
    (hs : EntropyCompletion.initiallyLogSparse G) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    EntropyCompletion.logVanishesOnNonedges G (EntropyCompletion.distanceKernel G x) := by
  rw [distanceKernel_eq_completion G hG hs hx hx1]
  exact completion_logVanishesOnNonedges G x

end PlanarHom.KernelContinuation

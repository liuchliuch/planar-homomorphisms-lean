import PlanarHom.ClosedFamilyPositiveLog
import PlanarHom.DistanceKernelAvailability
import PlanarHom.DistanceKernelMaximality

/-! Source4.2's family-membership and initial-sparsity clauses. The general
spectral-transfer closure is a source §4 closure rule, specialized only to the
already proved fixed-target spectral case of3.10; it does not assume distance
kernel membership or logarithmic sparsity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator Topology
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixLogCoefficients MaximumLogarithmicSupport EffectiveProductTransfer
open Filter
variable {q : ℕ}

/-- The source-assumed closure under effective spectral product transfer.
Uniform path simulation for powers is already proved independently. -/
structure EffectiveSpectralClosed (A : Set (Matrix (Fin q) (Fin q) ℝ)) : Prop where
  transfer_mem : ∀ H ∈ A, ∀ B : Matrix (Fin q) (Fin q) ℝ,
    H.PosDef → (∀ i j, IsAlgebraic ℚ (H i j)) → B.IsHermitian →
    (∀ i j, IsAlgebraic ℚ (B i j)) →
    (∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → ∀ i j, 0 < SpectralProductZeros.realPower H n i j) →
    ProductIdentities (SpectralProductZeros.realPower H) B → B ∈ A

/-- Closure applies to the actual rational kernel, with every transfer hypothesis
proved from H's positive connected logarithmic support. -/
theorem distanceKernel_mem (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : EffectiveSpectralClosed A) (H : Matrix (Fin q) (Fin q) ℝ) (hH : H ∈ A)
    (hpd : H.PosDef) (hAlg : ∀ i j, IsAlgebraic ℚ (H i j))
    (hconn : (logSupport H).Connected)
    (hpositive : ∀ i j, (logSupport H).Adj i j → 0 < EntropyCompletion.matrixLog H i j)
    (x : ℚ) : EntropyCompletion.distanceKernel (logSupport H) x ∈ A := by
  apply hA.transfer_mem H hH _ hpd hAlg
    (EntropyCompletion.distanceKernel_isHermitian _ _)
  · intro i j
    change IsAlgebraic ℚ ((x : ℝ) ^ (logSupport H).dist i j)
    exact (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) x).pow _
  · refine ⟨1, by omega, ?_⟩
    intro n hn i j
    rw [SpectralProductZeros.realPower_eq_exp_smul_log H hpd]
    exact exp_positive_time_entry_pos _ (cfc_predicate Real.log H) hconn hpositive n
      (by exact_mod_cast (Nat.zero_lt_of_lt hn)) i j
  · exact DistanceKernelProductIdentities.productIdentities H hpd hconn hpositive x

private theorem connected_of_all_entries_pos (H : Matrix (Fin q) (Fin q) ℝ)
    (hH : H.IsHermitian) [Nonempty (Fin q)] (hp : ∀ i j, 0 < H i j) :
    (offDiagonalSupport H hH).Connected := by
  constructor
  intro i j
  by_cases hij : i = j
  · subst j
    exact SimpleGraph.Reachable.refl _
  · exact (show (offDiagonalSupport H hH).Adj i j from ⟨hij, ne_of_gt (hp i j)⟩).reachable

/-- The distance-kernel candidate bound follows from membership and the same
maximum that selected M. Strict positivity retains numerical connectedness. -/
theorem rationalDistanceKernelEdgeBound (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : EffectiveSpectralClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M) (hAlg : ∀ i j, IsAlgebraic ℚ (M i j))
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    RationalDistanceKernelEdgeBound (logSupport M) := by
  have hc := logSupport_connected hM.posDef hM.connected
  letI : Nonempty (Fin q) := hc.nonempty
  refine ⟨1, by norm_num, ?_⟩
  intro x _ _ hpd hp
  exact hmax _ ⟨distanceKernel_mem A hA M hM.mem hM.posDef hAlg hc hpositive x,
    fun i j => (hp i j).le, hpd, connected_of_all_entries_pos _ hpd.1 hp⟩

/-- Source(4.1) follows for all small positive real parameters, through actual
log continuity and rational density, rather than an analyticity premise. -/
theorem initiallyLogSparse (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : EffectiveSpectralClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M) (hAlg : ∀ i j, IsAlgebraic ℚ (M i j))
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    EntropyCompletion.initiallyLogSparse (logSupport M) :=
  initiallyLogSparse_of_rational_distanceKernel_maximality _
    (logSupport_connected hM.posDef hM.connected)
    (rationalDistanceKernelEdgeBound A hA M hM hmax hAlg hpositive)

/-- **Lemma4.2, structural clauses.** Rational kernels belong to the source-closed
family; their PD and nonedge-log-zero properties hold together near zero. The
uniform machine assertion is DistanceKernelAvailability.uniformReduction. -/
theorem distanceKernel_near_zero (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : EffectiveSpectralClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M) (hAlg : ∀ i j, IsAlgebraic ℚ (M i j))
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
      (EntropyCompletion.distanceKernel (logSupport M) x).PosDef ∧
      EntropyCompletion.logVanishesOnNonedges (logSupport M)
        (EntropyCompletion.distanceKernel (logSupport M) x) := by
  have hc := logSupport_connected hM.posDef hM.connected
  obtain ⟨δ, hδ, hs⟩ := initiallyLogSparse A hA M hM hmax hAlg hpositive
  obtain ⟨η, hη, hp⟩ := Metric.eventually_nhds_iff.mp
    (EntropyCompletion.eventually_posDef_distanceKernel (logSupport M) hc)
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro x hx hxε
  exact ⟨hp (by simpa [Real.dist_eq, abs_of_pos hx] using (lt_min_iff.mp hxε).2),
    hs x hx (lt_min_iff.mp hxε).1⟩

end PlanarHom.ClosedMatrixFamily

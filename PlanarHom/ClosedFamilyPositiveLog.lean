import PlanarHom.MaximumSupportRigidity
import PlanarHom.MatrixPowerLogExponential

/-! Source4.1 for the explicitly closed matrix family of §4. Numerical maximum
bounds are derived from membership and maximality, rather than assumed for the
particular candidate. The two closure operations are literal rational CFC powers
and entrywise multiplication (the parallel-edge gadget). -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator Topology
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixLogCoefficients MaximumLogarithmicSupport
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Two source-assumed closure operations sufficient for Lemma4.1. -/
structure SpectralParallelClosed (A : Set (Matrix V V ℝ)) : Prop where
  rationalPower_mem : ∀ H ∈ A, H.PosDef → ∀ r : ℚ,
    cfc (fun x : ℝ => x ^ (r : ℝ)) H ∈ A
  entrywiseProduct_mem : ∀ H ∈ A, ∀ K ∈ A, (fun i j => H i j * K i j) ∈ A

/-- Precisely the maximization class C in source §4.1. Isolated singleton support
is included by ordinary graph connectedness. -/
structure Admissible (A : Set (Matrix V V ℝ)) (H : Matrix V V ℝ) : Prop where
  mem : H ∈ A
  nonneg : ∀ i j, 0 ≤ H i j
  posDef : H.PosDef
  connected : (offDiagonalSupport H posDef.1).Connected

def IsMaximum (A : Set (Matrix V V ℝ)) (M : Matrix V V ℝ) : Prop :=
  ∀ H, Admissible A H → (logSupport H).edgeFinset.card ≤ (logSupport M).edgeFinset.card

private theorem entrywisePower_mem (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (H : Matrix V V ℝ) (hH : H ∈ A) (s : ℕ) (hs : 0 < s) :
    (fun i j => H i j ^ s) ∈ A := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hz : s = 0
    · subst s
      simpa only [zero_add, pow_one] using hH
    · have hp := hA.entrywiseProduct_mem (fun i j => H i j ^ s) (ih (by omega)) H hH
      simpa only [pow_succ] using hp

/-- Every rational candidate is in A by the two actual source operations. -/
theorem schurExp_log_mem (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (M : Matrix V V ℝ) (hM : Admissible A M) (s : ℕ) (hs : 0 < s) (r : ℚ) :
    schurExp (EntropyCompletion.matrixLog M) s r ∈ A := by
  have hp := hA.rationalPower_mem M hM.mem hM.posDef r
  have hh := entrywisePower_mem A hA _ hp s hs
  convert hh using 1
  ext i j
  change NormedSpace.exp ℝ ((r : ℝ) • EntropyCompletion.matrixLog M) i j ^ s = _
  rw [← SpectralProductZeros.realPower_eq_exp_smul_log M hM.posDef (r : ℝ)]
  rfl

/-- The quantitative premise of the analytic core follows from the maximum over
C and source closure. No path/support conclusion occurs in these hypotheses. -/
theorem rationalSchurEdgeBound (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (M : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M) :
    RationalSchurEdgeBound (EntropyCompletion.matrixLog M) (cfc_predicate Real.log M) := by
  intro s hs _
  refine ⟨1, by norm_num, ?_⟩
  intro r _ _ hpd hconn hnonneg
  exact hmax _ ⟨schurExp_log_mem A hA M hM s hs r, hnonneg, hpd, hconn⟩

/-- **Lemma4.1.** The maximum is attained and can be chosen with connected
logarithmic support and strictly positive logarithmic entries on all its edges. -/
theorem exists_maximum_positive_log (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hne : ∃ H, Admissible A H) :
    ∃ M, Admissible A M ∧ IsMaximum A M ∧ (logSupport M).Connected ∧
      ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_logSupport {H | Admissible A H} hne
  have hR := logSupport_connected hM.posDef hM.connected
  have hbound := rationalSchurEdgeBound A hA M hM hmax
  have hL : (EntropyCompletion.matrixLog M).IsHermitian := cfc_predicate Real.log M
  obtain ⟨δ, hδ, hsupport⟩ := rational_schur_logSupport_eq_of_maximal
    (EntropyCompletion.matrixLog M) hL hR 2 (by decide) (by decide)
    (hbound 2 (by decide) (by decide))
  obtain ⟨r, hr, hrδ, hpd, hconn, hnn, _⟩ :=
    WheatstoneCoefficients.exists_positive_rat_of_eventually
      (eventually_schurExp_admissible (EntropyCompletion.matrixLog M) hL hR
        2 (by decide) (by decide)) hδ
  obtain ⟨_, heq, hpos⟩ := hsupport r hr hrδ
  let N := schurExp (EntropyCompletion.matrixLog M) 2 r
  have hN : Admissible A N := ⟨schurExp_log_mem A hA M hM 2 (by decide) r, hnn, hpd, hconn⟩
  refine ⟨N, hN, ?_, ?_, hpos⟩
  · intro H hH
    rw [show logSupport N = logSupport M from heq]
    exact hmax H hH
  · rw [show logSupport N = logSupport M from heq]
    exact hR

end PlanarHom.ClosedMatrixFamily

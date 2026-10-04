import PlanarHom.SignedThreeEasyClosed
import PlanarHom.SignedThreeStateDichotomy
import PlanarHom.RealRationalOracleDescent
import PlanarHom.RealApproximationRepresented
import PlanarHom.FixedRealFiniteReplacement
import Mathlib.Analysis.SpecificLimits.Basic

/-! NEW full signed three-state hard direction in the represented fixed-real
model. The exact easy set is closed; a fixed rational obstruction and the actual
A.3 oracle reduction transfer the frozen algebraic theorem with exact descent. -/
noncomputable section
open Classical Filter
open scoped Topology
namespace PlanarHom.FixedRealSmallState
open DensePolynomial FixedRealExtension Complexity RepresentedBit ProductCompatibility FixedRealApproximation
variable {q : ℕ}

 theorem closed_rational_obstruction (P : Matrix (Fin q) (Fin q) ℝ → Prop)
    (hclosed : IsClosed {M | P M}) (M : Matrix (Fin q) (Fin q) ℝ)
    (hs : ∀i j, M i j = M j i) (hbad : ¬P M) :
    ∃N : Matrix (Fin q) (Fin q) ℚ,
      (∀i j, N i j = N j i) ∧ (∀i j, N i j = 0 ↔ M i j = 0) ∧
      ¬P (fun i j => (N i j : ℝ)) ∧
      Compatible (fun p : Fin q × Fin q => M p.1 p.2) (fun p => (N p.1 p.2 : ℝ)) := by
  have hex (k : ℕ) := RelationApproximation.rational_approximation_with_zeros
    (fun p : Fin q × Fin q => M p.1 p.2) (1 / ((k : ℝ) + 1)) (by positivity)
  choose R hz ha hsg hc using hex
  have hsym (k : ℕ) (i j : Fin q) : R k (i,j) = R k (j,i) := by
    apply Rat.cast_injective (α := ℝ)
    exact RelationApproximation.equal_entries_of_compatible
      (fun p hp => by exact_mod_cast (hz k p).mpr hp) (hc k) (hs i j)
  have hlim : Tendsto (fun k i j => (R k (i,j) : ℝ)) atTop (𝓝 M) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.dist_eq] using (ha k (i,j)).le
  have hexBad : ∃k, ¬P (fun i j => (R k (i,j) : ℝ)) := by
    by_contra h
    have hall : ∀k, P (fun i j => (R k (i,j) : ℝ)) := by simpa using h
    exact hbad (hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hall))
  obtain ⟨k,hk⟩ := hexBad
  exact ⟨fun i j => R k (i,j), hsym k,fun i j => hz k (i,j),hk,hc k⟩

 variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
 theorem theorem23_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin 3) (Fin 3) K) (hs : ∀i j, M i j = M j i)
    (hbad : ¬SignedThreeState.ThreeStateEasy (fun i j => φ (M i j))) :
    RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1)) := by
  obtain ⟨N,hNs,hzero,hNbad,hcompat⟩ := closed_rational_obstruction
    SignedThreeState.ThreeStateEasy SignedThreeState.isClosed_threeStateEasy
    (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j)) hbad
  let L := rationalLanguage N
  have hhard : PromisedSharpPHard L.problem :=
    (SignedThreeState.theorem23_algebraic L (fun _ => rfl)
      (fun i j => by change (N i j : ℝ) = (N j i : ℝ); exact_mod_cast hNs i j)).2 hNbad
  have hr := (RepresentedBit.SharpPHard.ofCanonical hhard).trans (rationalOracleDescent basis N)
  have hm : HasProductMaps (fun p : Fin 3 × Fin 3 => M p.1 p.2)
      (fun p => (N p.1 p.2 : K)) := by
    apply hasProductMaps_of_compatible
    apply Compatible.of_injective_map φ
    simpa only [map_ratCast] using hcompat
  exact hr.trans (FixedRealMixedInterpolation.finiteReplacementReduction basis M
    (fun _ : Fin 1 => fun i j => (N i j : K)) (fun l : Fin 0 => l.elim0) (fun _ => 1)
    (fun _ i j h => by simp [(hzero i j).mpr (by simp [h])]) (fun _ => hm))

end PlanarHom.FixedRealSmallState

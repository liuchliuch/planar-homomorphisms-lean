import PlanarHom.ClockStructuralClassification
import PlanarHom.MainDichotomiesClosed
import PlanarHom.RankOneRealTractability

/-! Algebraic-matrix computational specialization of Corollary 12.5.
The pure-real parameter classification is complete in ClockStructuralClassification;
this file does not claim arbitrary-real exact computation for exponential entries. -/
noncomputable section
namespace PlanarHom.ClockModel
open AlgebraicProductInterpolation Complexity Structures

theorem zero_coupling_inFP {q:ℕ} (L:RealLanguage q 1 0)
    (hM:L.matrices 0=interaction q 0) : L.problem.InFP := by
  apply L.rankOne_inFP (fun _=>1)
  intro i j
  rw [hM,zero_interaction]
  simp

theorem corollary125_algebraic {q:ℕ} (hq:2≤q) {K:ℝ} (hK:K≠0)
    (L:RealLanguage q 1 0) (hM:L.matrices 0=interaction q K)
    (hw:∀i,0 < L.weights i) :
    (((q=2 ∨ q=4) ∧ ∃μ:ℝ,0 < μ ∧ ∀i,L.weights i=μ)→L.problem.InFP) ∧
    (¬((q=2 ∨ q=4) ∧ ∃μ:ℝ,0 < μ ∧ ∀i,L.weights i=μ)→PromisedSharpPHard L.problem) := by
  have hs:∀i j,L.matrices 0 i j=L.matrices 0 j i := by rw [hM]; exact symmetric q K
  have hp:∀i j,0≤L.matrices 0 i j := by rw [hM]; exact fun i j=>(positive q K i j).le
  have hc:=MainDichotomyScope.theorem13 L hs hp hw
  have he:PositiveVertexWeightClass (L.matrices 0) L.weights hs ↔
      (q=2 ∨ q=4) ∧ ∃μ:ℝ,0 < μ ∧ ∀i,L.weights i=μ := by
    simpa only [hM] using weighted_class_iff hq hK L.weights hw
  exact ⟨fun h=>hc.1 (he.mpr h),fun h=>hc.2 (fun h'=>h (he.mp h'))⟩

end PlanarHom.ClockModel

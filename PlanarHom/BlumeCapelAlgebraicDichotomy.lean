import PlanarHom.BlumeCapelMatrix
import PlanarHom.MainDichotomiesClosed
import PlanarHom.RankOneRealTractability

/-! Actual algebraic-source consequences of the pure arbitrary-real
Blume–Capel matrix obstruction. The fixed-real computational model remains
Appendix scope. Positive crystal/magnetic weights need no further restriction. -/
noncomputable section
namespace PlanarHom.BlumeCapel
open AlgebraicProductInterpolation Complexity Structures

theorem zero_coupling_inFP (L:RealLanguage 3 1 0)
    (hM:L.matrices 0=interaction 0) : L.problem.InFP := by
  apply L.rankOne_inFP (fun _=>1)
  intro i j
  rw [hM,zero_interaction]
  simp

theorem nonzero_coupling_hard {K:ℝ} (hK:K≠0) (L:RealLanguage 3 1 0)
    (hM:L.matrices 0=interaction K) (hw:∀i,0 < L.weights i) : PromisedSharpPHard L.problem := by
  have hs:∀i j,L.matrices 0 i j=L.matrices 0 j i := by rw [hM]; exact symmetric K
  have hp:∀i j,0≤L.matrices 0 i j := by rw [hM]; exact fun i j=>(positive K i j).le
  apply (MainDichotomyScope.theorem13 L hs hp hw).2
  intro h
  have h':PositiveVertexWeightClass (interaction K) L.weights (symmetric K) := by
    simpa only [hM] using h
  exact not_weighted_class hK L.weights h'

theorem corollary127_algebraic (K D F:ℝ) (L:RealLanguage 3 1 0)
    (hM:L.matrices 0=interaction K) (hw:L.weights=weight D F) :
    (K=0→L.problem.InFP) ∧ (K≠0→PromisedSharpPHard L.problem) := by
  constructor
  · intro hK; subst K; exact zero_coupling_inFP L hM
  · intro hK
    exact nonzero_coupling_hard hK L hM (fun i=>by rw [hw]; exact weight_positive D F i)

end PlanarHom.BlumeCapel

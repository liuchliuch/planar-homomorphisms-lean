import PlanarHom.CoupledIsingUniformFibers
import PlanarHom.PhysicalWeightedReindex
import PlanarHom.MainDichotomiesClosed

/-! Algebraic-matrix consequences of the full pure-real coupled-character
classification. Exponential source entries and weights must belong to the
source algebraic model; no arbitrary-real computational claim is inferred. -/
noncomputable section
namespace PlanarHom.CoupledIsing
open BinaryCharacters Structures AlgebraicProductInterpolation Complexity
variable {n m q:ℕ}

theorem corollary126_algebraic (a:Fin m→Space n) (ha:Function.Injective a)
    (hn:∀r,a r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0)
    (L:RealLanguage q 1 0) (e:Fin q≃Space n)
    (hM:∀i j,L.matrices 0 i j=interaction a J (e i) (e j))
    (hw:∀i,0 < L.weights i) :
    ((LinearIndependent F₂ a ∧ ∃μ:ℝ,0 < μ ∧
        ∀z,aggregatedWeight a (fun x=>L.weights (e.symm x)) z=μ)→L.problem.InFP) ∧
    (¬(LinearIndependent F₂ a ∧ ∃μ:ℝ,0 < μ ∧
        ∀z,aggregatedWeight a (fun x=>L.weights (e.symm x)) z=μ)→PromisedSharpPHard L.problem) := by
  have hs:∀i j,L.matrices 0 i j=L.matrices 0 j i := by
    intro i j; rw [hM,hM]; exact symmetric a J _ _
  have hp:∀i j,0≤L.matrices 0 i j := by
    intro i j; rw [hM]; exact (Real.exp_pos _).le
  have hsource:L.matrices 0=Twins.ReconstructedReindex.matrix (interaction a J) e:=
    funext (fun i=>funext (hM i))
  have hweight:(fun i=>L.weights (e.symm (e i)))=L.weights:=by simp
  have he:PositiveVertexWeightClass (L.matrices 0) L.weights hs ↔
      LinearIndependent F₂ a ∧ ∃μ:ℝ,0 < μ ∧
        ∀z,aggregatedWeight a (fun x=>L.weights (e.symm x)) z=μ := by
    have ht:=positiveVertexWeightClass_reindex_iff (interaction a J)
      (fun x=>L.weights (e.symm x)) (symmetric a J) e
    rw [hweight] at ht
    simpa only [hsource] using ht.trans (weighted_class_iff a ha hn J hJ _ (fun x=>hw _))
  have hc:=MainDichotomyScope.theorem13 L hs hp hw
  exact ⟨fun h=>hc.1 (he.mpr h),fun h=>hc.2 (fun h'=>h (he.mp h'))⟩

theorem corollary126_unit_algebraic (a:Fin m→Space n) (ha:Function.Injective a)
    (hn:∀r,a r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0)
    (L:RealLanguage q 1 0) (e:Fin q≃Space n)
    (hM:∀i j,L.matrices 0 i j=interaction a J (e i) (e j)) (hw:∀i,L.weights i=1) :
    (LinearIndependent F₂ a→L.problem.InFP) ∧
    (¬LinearIndependent F₂ a→PromisedSharpPHard L.problem) := by
  have hc:=corollary126_algebraic a ha hn J hJ L e hM (fun i=>by rw [hw]; exact zero_lt_one)
  constructor
  · intro h
    apply hc.1
    refine ⟨h,(2:ℝ)^(n-Matrix.rank a),by positivity,?_⟩
    intro z
    simpa only [hw] using unit_aggregatedWeight a z
  · intro h
    exact hc.2 (fun hh=>h hh.1)

end PlanarHom.CoupledIsing

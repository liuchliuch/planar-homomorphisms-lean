import PlanarHom.FixedRealLemmaA10
import PlanarHom.FixedRealBipartiteCoreEasy
import PlanarHom.FixedRealBipartiteRightHard

/-! A.11's full ordinary symmetric-double endpoint. The two side constants are
independent, and either nonconstant weight vector triggers an actual same-side
Gram obstruction in the prescribed fixed-real source field. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealLemmaA11
open DensePolynomial Complexity FixedRealExtension RepresentedBit Boolean PositiveRealCore
variable {n e d:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

def problem (basis:Module.Basis (Fin e) (RationalFunction n) F) (c:F) (ρ:Fin d→F) (μ ν:Cube d→F) : Problem :=
  FixedRealBipartiteLeftHard.problem basis (c • FixedRealTensorCoreEasy.tensor ρ) μ ν

theorem constant_inFP (basis:Module.Basis (Fin e) (RationalFunction n) F) (c:F) (ρ:Fin d→F)
    (μ ν:Cube d→F) (hμ:∀i j,μ i=μ j) (hν:∀i j,ν i=ν j) : (problem basis c ρ μ ν).InFP := by
  let α:=μ (fun _=>false)
  let β:=ν (fun _=>false)
  have hm:μ=(fun _=>α):=funext (fun i=>hμ i _)
  have hn:ν=(fun _=>β):=funext (fun i=>hν i _)
  let f:ℚ→+*F:=(algebraMap (RationalFunction n) F).comp
    ((algebraMap (Poly n) (RationalFunction n)).comp (qHom n))
  have hh:=FixedRealBipartiteCoreEasy.inFP basis f c α β ρ
  have hu:(BooleanTensorFPClosure.emptyUnaries:Fin 0→(Cube d⊕Cube d)→F)=(fun l:Fin 0=>l.elim0) := by
    funext l; exact l.elim0
  simpa only [problem,FixedRealBipartiteLeftHard.problem,FixedRealComponents.problem,
    FixedRealBipartiteCoreEasy.problem,FixedRealBipartiteCoreEasy.double,FixedRealBipartiteLeftHard.double,
    FixedRealBipartiteCoreEasy.weights,hu,hm,hn] using hh

theorem nonconstant_hard (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (hc:0<algebraMap F ℝ c) (ρ:Fin d→F)
    (hρ:∀j,0<algebraMap F ℝ (ρ j)) (hne:∀j,algebraMap F ℝ (ρ j)≠1)
    (μ ν:Cube d→F) (hμ:∀i,0<algebraMap F ℝ (μ i)) (hν:∀i,0<algebraMap F ℝ (ν i))
    (hnon:(∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j)) : SharpPHard (problem basis c ρ μ ν) := by
  let B:=c • FixedRealTensorCoreEasy.tensor ρ
  let cR:=algebraMap F ℝ c
  let ρR:=fun j=>algebraMap F ℝ (ρ j)
  have he:FixedRealBipartiteLeftHard.realB B=scaledTensor cR ρR := by
    ext i j
    change algebraMap F ℝ (c*FixedRealTensorCoreEasy.tensor ρ i j)=cR*Boolean.tensor ρR i j
    rw [map_mul,FixedRealLemmaA10.tensor_real]
  have hB:IsUnit (FixedRealBipartiteLeftHard.realB B) := by
    rw [he,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
    exact scaledTensor_det_ne_zero cR hc ρR hρ hne
  have hnonR:(∃i j,FixedRealBipartiteLeftHard.realW μ i≠FixedRealBipartiteLeftHard.realW μ j) ∨
      (∃i j,FixedRealBipartiteLeftHard.realW ν i≠FixedRealBipartiteLeftHard.realW ν j) := by
    rcases hnon with ⟨i,j,hij⟩|⟨i,j,hij⟩
    · exact Or.inl ⟨i,j,fun h=>hij ((algebraMap F ℝ).injective h)⟩
    · exact Or.inr ⟨i,j,fun h=>hij ((algebraMap F ℝ).injective h)⟩
  obtain ⟨hpX,hpY,hposX,hposY,hdiag⟩:=bipartite_ising_core cR hc ρR hρ hne
    (FixedRealBipartiteLeftHard.realW μ) (FixedRealBipartiteLeftHard.realW ν) hμ hν hnonR
  rw [←he] at hpX hpY hposX hposY hdiag
  rcases hdiag with hleft|hright
  · exact FixedRealBipartiteLeftHard.left_hard basis B μ ν hμ hν hB hpX hposX hleft
  · exact FixedRealBipartiteLeftHard.right_hard basis B μ ν hμ hν hB hpY hposY hright

/-- Exact ordinary-input statement, including different constants on the sides. -/
theorem lemmaA11_ordinary (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (hc:0<algebraMap F ℝ c) (ρ:Fin d→F)
    (hρ:∀j,0<algebraMap F ℝ (ρ j)) (hne:∀j,algebraMap F ℝ (ρ j)≠1)
    (μ ν:Cube d→F) (hμ:∀i,0<algebraMap F ℝ (μ i)) (hν:∀i,0<algebraMap F ℝ (ν i)) :
    (((∀i j,μ i=μ j) ∧ (∀i j,ν i=ν j))→(problem basis c ρ μ ν).InFP) ∧
      (((∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j))→SharpPHard (problem basis c ρ μ ν)) :=
  ⟨fun h=>constant_inFP basis c ρ μ ν h.1 h.2,nonconstant_hard basis c hc ρ hρ hne μ ν hμ hν⟩

end PlanarHom.FixedRealLemmaA11

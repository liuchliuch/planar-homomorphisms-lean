import PlanarHom.BipartiteTensorWeightHardnessConditional
import PlanarHom.WeightedBlockTractabilityConditional
import PlanarHom.TypedRealLanguagePresentation
import PlanarHom.HomogeneousSourceOrientationReduction
import PlanarHom.PositiveIsingFoundationClosed

/-! NEW exact color/side chart and constant-side tractable form for Lemma 9.3.
The two positive side constants remain independent, including when unequal. -/
noncomputable section
open Classical
namespace PlanarHom.PrescribedTensorWeight
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PositiveRealCore Structures PrescribedDomains HomogeneousSourceOrientation FixedRealRootRestrictions
variable {q d:ℕ}

 def side (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (i:Fin q) : Bool :=
  Sum.elim (fun _=>false) (fun _=>true) (e i)

 def problem (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0) : PromiseProblem :=
  L.typedProblem (Bipartite.domains (side e)) sidePolicies emptyPolicies

 def sideChart (I:Type) : I⊕I≃(Fin 1⊕Fin 1)×I where
  toFun := Sum.elim (fun x=>(.inl 0,x)) (fun x=>(.inr 0,x))
  invFun p := Sum.elim (fun _=>.inl p.2) (fun _=>.inr p.2) p.1
  left_inv x := by cases x <;> rfl
  right_inv p := by
    rcases p with ⟨i|i,x⟩ <;> have hi:i=0:=Subsingleton.elim _ _ <;> subst i <;> rfl

 theorem matrix_crosses (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (ρ:Fin d→ℝ)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j)) :
    ∀i j,L.matrices 0 i j≠0→side e i≠side e j := by
  intro i j hn
  rw [hM] at hn
  cases hi:e i <;> cases hj:e j <;> simp_all [side,doubleMatrix]

 theorem constant_sides_allowed (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) (hne:∀r,ρ r≠1)
    (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i))
    (a b:ℝ) (ha:∀i,μ i=a) (hb:∀i,ν i=b) :
    AllowedWeightedBlock (L.matrices 0) L.weights := by
  let chart:=e.trans (sideChart (Boolean.Cube d))
  have hapos:0<a:=by rw [←ha (fun _=>false)];exact hμ _
  have hbpos:0<b:=by rw [←hb (fun _=>false)];exact hν _
  apply AllowedWeightedBlock.bipartite 1 1 d (by decide) (by decide)
    (fun _=>c) (fun _=>a) (fun _=>1) (fun _=>b) ρ
    (fun _=>hc) (fun _=>by norm_num) (fun _=>hapos) (fun _=>hbpos)
    (fun r=>⟨hρ r,hne r⟩) chart
  · intro i j
    rw [hM]
    cases hi:e i <;> cases hj:e j <;>
      simp [chart,sideChart,hi,hj,doubleMatrix,scaledTensor,bipartiteAmplitude,Boolean.tensor_symm]
  · intro i
    rw [hw]
    cases hi:e i <;> simp [chart,sideChart,hi,ha,hb]

 theorem constant_sides_ordinary_inFP (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) (hne:∀r,ρ r≠1)
    (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i))
    (a b:ℝ) (ha:∀i,μ i=a) (hb:∀i,ν i=b) : L.problem.InFP := by
  have hf:=WeightedBlockTractability.allowedWeightedBlock_inFP_of_ising
    BooleanTensorEasyAssembly.positiveIsingFoundation L.field L.basis (L.matricesK 0) L.weightsK
    (constant_sides_allowed e L c hc ρ hρ hne μ ν hμ hν hM hw a b ha hb)
  have hm:L.matricesK=(fun _:Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hm,hu]
  exact hf

end PlanarHom.PrescribedTensorWeight

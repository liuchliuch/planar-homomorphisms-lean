import PlanarHom.PrescribedTensorWeightStructure
import PlanarHom.OrdinaryToPrescribedBipartite

/-! NEW full prescribed-side tensor-weight assembly for Lemma 9.3.
The actual computed two-orientation raw reduction supplies hardness on the
original prescribed-domain problem. The two side constants may differ.
The independent all-q Potts foundation remains explicit only in this internal
assembly; the final wrapper will instantiate its proved source theorem. -/
noncomputable section
open Classical
namespace PlanarHom.PrescribedTensorWeight
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PositiveRealCore Structures PrescribedDomains HomogeneousSourceOrientation FixedRealRootRestrictions
variable {q d:ℕ}

 def SideConstant (μ ν:Boolean.Cube d→ℝ) : Prop := ∃a b,(∀i,μ i=a) ∧ (∀i,ν i=b)

 theorem sideConstant_or_nonconstant (μ ν:Boolean.Cube d→ℝ) :
    SideConstant μ ν ∨ (∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j) := by
  by_cases hm:∃i j,μ i≠μ j
  · exact Or.inr (Or.inl hm)
  by_cases hn:∃i j,ν i≠ν j
  · exact Or.inr (Or.inr hn)
  refine Or.inl ⟨μ (fun _=>false),ν (fun _=>false),?_,?_⟩
  · intro i
    by_contra h
    exact hm ⟨i,fun _=>false,h⟩
  · intro i
    by_contra h
    exact hn ⟨i,fun _=>false,h⟩

 theorem problem_eq (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0) :
    problem e L=OrdinaryToPrescribedBipartite.prescribedProblem L.basis (L.matricesK 0) L.weightsK (side e) := by
  have hm:L.matricesK=(fun _:Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  unfold problem RealLanguage.typedProblem OrdinaryToPrescribedBipartite.prescribedProblem
  rw [hm,hu]

 def forward (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (ρ:Fin d→ℝ)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j)) :
    PromisePolyTimeTuringReduction L.problem (problem e L) := by
  have hx:∀i j,L.matricesK 0 i j≠0→side e i≠side e j:=by
    intro i j hn
    exact matrix_crosses e L c ρ hM i j (fun hz=>hn (Subtype.ext hz))
  have hh:=OrdinaryToPrescribedBipartite.forward L.basis (L.matricesK 0) L.weightsK (side e) hx
  have hm:L.matricesK=(fun _:Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  rw [problem_eq]
  change PromisePolyTimeTuringReduction (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK) _
  rw [hm,hu]
  exact hh

 def reverse (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (ρ:Fin d→ℝ) (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i)) :
    PromisePolyTimeTuringReduction (problem e L) L.problem := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hx:∀i j,L.matricesK 0 i j≠0→side e i≠side e j:=by
    intro i j hn
    exact matrix_crosses e L c ρ hM i j (fun hz=>hn (Subtype.ext hz))
  have hwK:∀i,0<L.weightsK i:=by
    intro i
    change 0<L.weights i
    rw [hw]
    cases e i <;> first | exact hμ _ | exact hν _
  have hh:=OrdinaryToPrescribedBipartite.reverse L.basis (L.matricesK 0) L.weightsK hwK (side e) hx
  have hm:L.matricesK=(fun _:Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  rw [problem_eq]
  change PromisePolyTimeTuringReduction _ (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK)
  rw [hm,hu]
  exact hh

 theorem constant_sides_inFP (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) (hne:∀r,ρ r≠1)
    (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i)) (hconst:SideConstant μ ν) :
    (problem e L).InFP := by
  obtain ⟨a,b,ha,hb⟩:=hconst
  exact (reverse e L c ρ μ ν hμ hν hM hw).inFP
    (constant_sides_ordinary_inFP e L c hc ρ hρ hne μ ν hμ hν hM hw a b ha hb)

 theorem nonconstant_weights_hard_of_potts (hPotts:PositivePottsFoundation)
    (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) (hne:∀r,ρ r≠1)
    (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i))
    (hnon:(∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j)) : PromisedSharpPHard (problem e L) :=
  (BipartiteTensorWeight.nonconstant_weights_hard_of_potts hPotts e L c hc ρ hρ hne μ ν hμ hν hM hw hnon).trans
    (forward e L c ρ hM)

 theorem lemma93_of_potts (hPotts:PositivePottsFoundation)
    (e:Fin q≃Boolean.Cube d⊕Boolean.Cube d) (L:RealLanguage q 1 0)
    (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) (hne:∀r,ρ r≠1)
    (μ ν:Boolean.Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀i,0<ν i)
    (hM:∀i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw:∀i,L.weights i=Sum.elim μ ν (e i)) :
    (SideConstant μ ν→(problem e L).InFP) ∧
      (¬SideConstant μ ν→PromisedSharpPHard (problem e L)) := by
  refine ⟨constant_sides_inFP e L c hc ρ hρ hne μ ν hμ hν hM hw,?_⟩
  intro hnot
  obtain h|h:=sideConstant_or_nonconstant μ ν
  · exact (hnot h).elim
  · exact nonconstant_weights_hard_of_potts hPotts e L c hc ρ hρ hne μ ν hμ hν hM hw h

end PlanarHom.PrescribedTensorWeight

import PlanarHom.BodyUnconditionalClassification
import PlanarHom.NonnegativeVertexWeightDichotomyConditional
import PlanarHom.DomainDoublingLiteralCorollary
import PlanarHom.PrescribedTensorWeightDichotomy
import PlanarHom.DiagonalSeparationProposition
import PlanarHom.ZeroOneTheorem71Closed
import PlanarHom.CenteredLogStructural

/-! NEW unconditional body corollaries, using the actual proved foundations. -/
noncomputable section
set_option autoImplicit false
open Classical
open PlanarHom.AlgebraicProductInterpolation PlanarHom.AlgebraicProductInterpolation.RealLanguage
open PlanarHom.Complexity PlanarHom.Structures

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
variable {q : ℕ}

theorem corollary112 (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0≤L.weights i) :
    (L.SurvivingWeightedClass hs → L.problem.InFP) ∧
    (¬L.SurvivingWeightedClass hs → PromisedSharpPHard L.problem) := by
  have hh:=L.positiveLanguage.theorem13_of_potts positivePottsFoundation
    (fun i j=>hs (L.positiveIndex i).val (L.positiveIndex j).val)
    (fun i j=>hnn _ _) L.positiveLanguage_weights
  refine ⟨L.surviving_weighted_class_inFP hs hw,?_⟩
  intro hbad
  exact (hh.2 hbad).trans (L.restoreZeroColorsReduction hw)

theorem corollary112_dichotomy (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0≤L.weights i) :
    L.problem.InFP ∨ PromisedSharpPHard L.problem := by
  by_cases hc : L.SurvivingWeightedClass hs
  · exact Or.inl ((L.corollary112_of_potts positivePottsFoundation hs hnn hw).1 hc)
  · exact Or.inr ((L.corollary112_of_potts positivePottsFoundation hs hnn hw).2 hc)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

namespace PlanarHom.DomainDoublingClassification
variable {q x y : ℕ}

theorem corollary122_bipartite (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0<L.weights i) :
    (PositiveVertexWeightClass ((doubledLanguage L).matrices 0) (doubledLanguage L).weights (doubled_symm L hs) →
      (bipartiteProblem L).InFP) ∧
    (¬PositiveVertexWeightClass ((doubledLanguage L).matrices 0) (doubledLanguage L).weights (doubled_symm L hs) →
      PromisedSharpPHard (bipartiteProblem L)) := by
  have h:=(doubledLanguage L).theorem13_of_potts positivePottsFoundation (doubled_symm L hs) (doubled_nonneg L hnn) (fun i=>hw _)
  exact ⟨fun hc=>(toDoubled L).inFP (h.1 hc),fun hc=>(h.2 hc).trans (fromDoubled L)⟩

theorem corollary122_prescribed (L : RealLanguage q 1 0)
    (side : Fin q→Bool) (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0<L.weights i) :
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → (prescribedProblem L side).InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard (prescribedProblem L side)) := by
  have h:=L.theorem13_of_potts positivePottsFoundation hs hnn hw
  exact ⟨fun hc=>(prescribedReverse L side hcross hw).inFP (h.1 hc),
    fun hc=>(h.2 hc).trans (prescribedForward L side hcross)⟩

theorem corollary122_bipartite_unweighted (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hunit : ∀i,L.weights i=1) :
    (NonnegativeClass ((doubledLanguage L).matrices 0) → (bipartiteProblem L).InFP) ∧
    (¬NonnegativeClass ((doubledLanguage L).matrices 0) → PromisedSharpPHard (bipartiteProblem L)) := by
  have h:=(doubledLanguage L).theorem11_of_potts positivePottsFoundation (fun i=>hunit _) (doubled_symm L hs) (doubled_nonneg L hnn)
  exact ⟨fun hc=>(toDoubled L).inFP (h.1 hc),fun hc=>(h.2 hc).trans (fromDoubled L)⟩

theorem corollary122_prescribed_unweighted (L : RealLanguage q 1 0)
    (side : Fin q→Bool) (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hunit : ∀i,L.weights i=1) :
    (NonnegativeClass (L.matrices 0) → (prescribedProblem L side).InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard (prescribedProblem L side)) := by
  have h:=L.theorem11_of_potts positivePottsFoundation hunit hs hnn
  have hw : ∀i,0<L.weights i:=by intro i; rw [hunit]; norm_num
  exact ⟨fun hc=>(prescribedReverse L side hcross hw).inFP (h.1 hc),
    fun hc=>(h.2 hc).trans (prescribedForward L side hcross)⟩

end PlanarHom.DomainDoublingClassification

namespace PlanarHom.DomainDoublingClassification
variable {q x y : ℕ}

theorem corollary122_rectangular
    (V : Matrix (Fin x) (Fin y) ℝ) (μ : Fin x→ℝ) (ν : Fin y→ℝ)
    (hV : ∀i j,IsAlgebraic ℚ (V i j)) (hμ : ∀i,IsAlgebraic ℚ (μ i)) (hν : ∀i,IsAlgebraic ℚ (ν i))
    (hnn : ∀i j,0≤V i j) (hμpos : ∀i,0<μ i) (hνpos : ∀i,0<ν i) :
    let L:=rectangularLanguage V μ ν hV hμ hν
    (PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      (prescribedProblem L rectangularSide).InFP) ∧
    (¬PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      PromisedSharpPHard (prescribedProblem L rectangularSide)) := by
  dsimp only
  apply corollary122_prescribed_of_potts positivePottsFoundation (rectangularLanguage V μ ν hV hμ hν)
    rectangularSide (rectangular_crosses V) (rectangular_symm V) (rectangular_nonneg V hnn)
  intro i
  change 0<Sum.elim μ ν (rectangularIndex x y i)
  cases rectangularIndex x y i <;> first | exact hμpos _ | exact hνpos _

end PlanarHom.DomainDoublingClassification

namespace PlanarHom.PrescribedTensorWeight
open Boolean PositiveRealCore
variable {q d : ℕ}

theorem lemma93 
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
  · exact nonconstant_weights_hard_of_potts positivePottsFoundation e L c hc ρ hρ hne μ ν hμ hν hM hw h

end PlanarHom.PrescribedTensorWeight

namespace PlanarHom.GadgetDiagonalSeparation
variable {q : ℕ}

theorem proposition25 (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) :
    ((∀i j,0<L.matrices 0 i j)→Function.Injective (fun i=>L.matrices 0 i i)→
      ((L.matrices 0).rank=1→L.problem.InFP) ∧
        (1<(L.matrices 0).rank→PromisedSharpPHard L.problem)) ∧
    (Separates (L.matrices 0)→
      (SupportRankCondition (L.matrices 0) hs→L.problem.InFP) ∧
        (¬SupportRankCondition (L.matrices 0) hs→PromisedSharpPHard L.problem)) :=
  ⟨fun hp hd=>proposition25i_of_potts positivePottsFoundation L hunit hs hp hd,
    fun hsep=>proposition25ii_of_potts positivePottsFoundation L hunit hs hnn hsep⟩

end PlanarHom.GadgetDiagonalSeparation

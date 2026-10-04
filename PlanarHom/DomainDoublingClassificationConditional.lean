import PlanarHom.ComputedDomainDoublingReduction
import PlanarHom.MainDichotomyFinalAssembly
import PlanarHom.TypedRealLanguagePresentation
import PlanarHom.ActualTwinReduction

/-! NEW Corollary 12.2 assembly. The actual doubled-language reductions and
prescribed-side reductions carry the full weighted classification. The sole
Potts foundation is explicit here and discharged in BodyCorollariesClosed.lean. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.DomainDoublingClassification
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open AlgebraicProductInterpolation.RealLanguage Structures
open PrescribedDomains HomogeneousSourceOrientation FixedRealRootRestrictions
variable {q : ℕ}

def doubleIndex (q : ℕ) : Fin (2*q)≃Bool×Fin q := Fintype.equivOfCardEq (by simp)

def doubledLanguage (L : RealLanguage q 1 0) : RealLanguage (2*q) 1 0 where
  matrices _ i j:=ComputedDomainDoubling.matrix (L.matrices 0) (doubleIndex q i) (doubleIndex q j)
  unaries u:=u.elim0
  weights i:=L.weights (doubleIndex q i).2
  matrices_algebraic _ i j:=by
    unfold ComputedDomainDoubling.matrix
    split
    · exact isAlgebraic_zero
    · exact L.matrices_algebraic 0 _ _
  unaries_algebraic u:=u.elim0
  weights_algebraic i:=L.weights_algebraic _

def doubledMatrixK (L : RealLanguage q 1 0) : Matrix (Fin (2*q)) (Fin (2*q)) L.field :=
  fun i j=>ComputedDomainDoubling.matrix (L.matricesK 0) (doubleIndex q i) (doubleIndex q j)

def doubledWeightsK (L : RealLanguage q 1 0) : Fin (2*q)→L.field := fun i=>L.weightsK (doubleIndex q i).2

theorem doubledMatrixK_val (L : RealLanguage q 1 0) (i j : Fin (2*q)) :
    (doubledMatrixK L i j:ℝ)=(doubledLanguage L).matrices 0 i j := by
  simp only [doubledMatrixK,doubledLanguage,ComputedDomainDoubling.matrix]
  split_ifs <;> rfl

def bipartiteProblem (L : RealLanguage q 1 0) : PromiseProblem :=
  ComputedDomainDoubling.bipartiteProblem L.basis (L.matricesK 0) L.weightsK

def toDoubled (L : RealLanguage q 1 0) :
    PromisePolyTimeTuringReduction (bipartiteProblem L) (doubledLanguage L).problem := by
  have hr:=ComputedDomainDoubling.bipartiteToDouble L.basis (L.matricesK 0) L.weightsK
  have he:=ActualTwins.homogeneousIdentityReduction L.basis
    (ComputedDomainDoubling.matrix (L.matricesK 0)) (ComputedDomainDoubling.weights L.weightsK)
    (doubledMatrixK L) (doubledWeightsK L)
    (fun g hg=>((g.toMultiGraph hg).partition_reindexColors
      (ComputedDomainDoubling.matrix (L.matricesK 0)) (ComputedDomainDoubling.weights L.weightsK)
      (doubleIndex q)).symm)
  have hp:=(doubledLanguage L).presentationMapReduction L.field L.basis
    (fun _ : Fin 1=>doubledMatrixK L) (fun u : Fin 0=>u.elim0) (doubledWeightsK L)
    (fun _ i j=>doubledMatrixK_val L i j) (fun u=>u.elim0) (fun _=>rfl)
  exact hr.trans (he.trans hp)

def fromDoubled (L : RealLanguage q 1 0) :
    PromisePolyTimeTuringReduction (doubledLanguage L).problem (bipartiteProblem L) := by
  have hp:=(doubledLanguage L).presentationDescentReduction L.field L.basis
    (fun _ : Fin 1=>doubledMatrixK L) (fun u : Fin 0=>u.elim0) (doubledWeightsK L)
    (fun _ i j=>doubledMatrixK_val L i j) (fun u=>u.elim0) (fun _=>rfl)
  have he:=ActualTwins.reindexReduction L.basis
    (ComputedDomainDoubling.matrix (L.matricesK 0)) (ComputedDomainDoubling.weights L.weightsK) (doubleIndex q)
  exact hp.trans (he.trans (ComputedDomainDoubling.doubleToBipartite L.basis (L.matricesK 0) L.weightsK))

theorem doubled_symm (L : RealLanguage q 1 0) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) :
    ∀i j,(doubledLanguage L).matrices 0 i j=(doubledLanguage L).matrices 0 j i := by
  intro i j
  simp only [doubledLanguage,ComputedDomainDoubling.matrix]
  split_ifs <;> first | rfl | exact hs _ _ | simp_all

theorem doubled_nonneg (L : RealLanguage q 1 0) (hnn : ∀i j,0≤L.matrices 0 i j) :
    ∀i j,0≤(doubledLanguage L).matrices 0 i j := by
  intro i j
  simp only [doubledLanguage,ComputedDomainDoubling.matrix]
  split <;> first | exact le_rfl | exact hnn _ _

theorem corollary122_bipartite_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0<L.weights i) :
    (PositiveVertexWeightClass ((doubledLanguage L).matrices 0) (doubledLanguage L).weights (doubled_symm L hs) →
      (bipartiteProblem L).InFP) ∧
    (¬PositiveVertexWeightClass ((doubledLanguage L).matrices 0) (doubledLanguage L).weights (doubled_symm L hs) →
      PromisedSharpPHard (bipartiteProblem L)) := by
  have h:=(doubledLanguage L).theorem13_of_potts hPotts (doubled_symm L hs) (doubled_nonneg L hnn) (fun i=>hw _)
  exact ⟨fun hc=>(toDoubled L).inFP (h.1 hc),fun hc=>(h.2 hc).trans (fromDoubled L)⟩

def prescribedProblem (L : RealLanguage q 1 0) (side : Fin q→Bool) : PromiseProblem :=
  OrdinaryToPrescribedBipartite.prescribedProblem L.basis (L.matricesK 0) L.weightsK side

def prescribedForward (L : RealLanguage q 1 0) (side : Fin q→Bool)
    (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j) :
    PromisePolyTimeTuringReduction L.problem (prescribedProblem L side) := by
  have hx : ∀i j,L.matricesK 0 i j≠0 → side i≠side j:=fun i j hn=>hcross i j (fun hz=>hn (Subtype.ext hz))
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  change PromisePolyTimeTuringReduction (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK) _
  rw [hm,hu]
  exact OrdinaryToPrescribedBipartite.forward L.basis _ _ side hx

def prescribedReverse (L : RealLanguage q 1 0) (side : Fin q→Bool)
    (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j) (hw : ∀i,0<L.weights i) :
    PromisePolyTimeTuringReduction (prescribedProblem L side) L.problem := by
  letI : IsStrictOrderedRing L.field:=Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hx : ∀i j,L.matricesK 0 i j≠0 → side i≠side j:=fun i j hn=>hcross i j (fun hz=>hn (Subtype.ext hz))
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  change PromisePolyTimeTuringReduction _ (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK)
  rw [hm,hu]
  exact OrdinaryToPrescribedBipartite.reverse L.basis _ _ hw side hx

theorem corollary122_prescribed_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (side : Fin q→Bool) (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0<L.weights i) :
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → (prescribedProblem L side).InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard (prescribedProblem L side)) := by
  have h:=L.theorem13_of_potts hPotts hs hnn hw
  exact ⟨fun hc=>(prescribedReverse L side hcross hw).inFP (h.1 hc),
    fun hc=>(h.2 hc).trans (prescribedForward L side hcross)⟩

theorem corollary122_bipartite_unweighted_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hunit : ∀i,L.weights i=1) :
    (NonnegativeClass ((doubledLanguage L).matrices 0) → (bipartiteProblem L).InFP) ∧
    (¬NonnegativeClass ((doubledLanguage L).matrices 0) → PromisedSharpPHard (bipartiteProblem L)) := by
  have h:=(doubledLanguage L).theorem11_of_potts hPotts (fun i=>hunit _) (doubled_symm L hs) (doubled_nonneg L hnn)
  exact ⟨fun hc=>(toDoubled L).inFP (h.1 hc),fun hc=>(h.2 hc).trans (fromDoubled L)⟩

theorem corollary122_prescribed_unweighted_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (side : Fin q→Bool) (hcross : ∀i j,L.matrices 0 i j≠0 → side i≠side j)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hunit : ∀i,L.weights i=1) :
    (NonnegativeClass (L.matrices 0) → (prescribedProblem L side).InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard (prescribedProblem L side)) := by
  have h:=L.theorem11_of_potts hPotts hunit hs hnn
  have hw : ∀i,0<L.weights i:=by intro i; rw [hunit]; norm_num
  exact ⟨fun hc=>(prescribedReverse L side hcross hw).inFP (h.1 hc),
    fun hc=>(h.2 hc).trans (prescribedForward L side hcross)⟩

end PlanarHom.DomainDoublingClassification

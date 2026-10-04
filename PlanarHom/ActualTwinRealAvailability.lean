import PlanarHom.ActualTwinRemoval
import PlanarHom.PositiveWeightRealAvailability
import PlanarHom.RootedRealComponentAvailability

/-! Source-facing Corollary 3.8 for the fixed real-algebraic source language.
The original source alone chooses the number field and exact output basis.
Identical rows mean equality of numerical entries, including their signs.
The exact quotient identity keeps the zero class; the computational endpoint
then deletes it and removes positive weights under precisely the source row
hypothesis, which is proved automatically in the zero–one case. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode ActualTwins SpectralFieldPresentation
variable {q : ℕ} (L : RealLanguage q 1 0)

theorem actualTwin_symmetryK (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    ∀ i j,L.matricesK 0 i j=L.matricesK 0 j i :=
  fun i j => Subtype.ext (hs i j)

/-- The finite field representation identifies exactly the original real rows. -/
theorem actualTwin_rows_eq_iff (i j : Fin q) :
    L.matricesK 0 i=L.matricesK 0 j ↔ L.matrices 0 i=L.matrices 0 j := by
  constructor
  · intro h
    funext k
    exact congrArg L.field.val (congrFun h k)
  · intro h
    funext k
    exact Subtype.ext (congrFun h k)

def actualTwinMatrixK (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :=
  reducedMatrix (L.matricesK 0) (L.actualTwin_symmetryK hs)

def actualTwinMatrix (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :=
  realMatrix (L.actualTwinMatrixK hs)

/-- The final real matrix B is literally the representative submatrix of A. -/
theorem actualTwinMatrix_eq_representatives
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (i j : Fin (reducedCount (L.matricesK 0) (L.actualTwin_symmetryK hs))) :
    L.actualTwinMatrix hs i j =
      L.matrices 0 (representative (L.matricesK 0) (L.actualTwin_symmetryK hs) i)
        (representative (L.matricesK 0) (L.actualTwin_symmetryK hs) j) :=
  congrArg L.field.val
    (reducedMatrix_eq_representatives (L.matricesK 0) (L.actualTwin_symmetryK hs) i j)

def actualTwinWeightK (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :=
  reducedWeight (L.matricesK 0) (L.actualTwin_symmetryK hs) L.weightsK

/-- The source's nonzero-matrix condition makes the final color set nonempty. -/
theorem actualTwin_card_pos (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hA : L.matrices 0 ≠ 0) :
    0 < reducedCount (L.matricesK 0) (L.actualTwin_symmetryK hs) := by
  apply reducedCount_pos
  intro h
  apply hA
  funext i j
  exact congrArg L.field.val (congrFun (congrFun h i) j)

/-- The full quotient oracle retains its zero-row class if one exists. -/
def actualQuotientProblem (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) : PromiseProblem :=
  evaluationProblem L.basis
    (fun _ : Fin 1 => Twins.quotientMatrix (L.matricesK 0) (L.actualTwin_symmetryK hs))
    (fun u : Fin 0 => Fin.elim0 u) (Twins.quotientWeight (L.matricesK 0) L.weightsK)

def weightedActualTwinProblem (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) : PromiseProblem :=
  evaluationProblem L.basis (fun _ : Fin 1 => L.actualTwinMatrixK hs)
    (fun u : Fin 0 => Fin.elim0 u) (L.actualTwinWeightK hs)

/-- Ordinary unweighted evaluation of the nonzero actual twin quotient. -/
def actualTwinProblem (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) : PromiseProblem :=
  evaluationProblem L.basis (fun _ : Fin 1 => L.actualTwinMatrixK hs)
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)

/-- The literal real source identity, for every graph including empty inputs,
loops and isolated vertices. Its color set includes the zero-row class. -/
theorem corollary38_identity {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    G.partition (L.matrices 0) L.weights =
      G.partition (Twins.quotientMatrix (L.matrices 0) hs)
        (Twins.quotientWeight (L.matrices 0) L.weights) :=
  Twins.partition_canonicalQuotient G (L.matrices 0) L.weights hs

/-- The number-field full quotient answers are exactly the literal real
quotient partition values, even though the computational representation uses
the original source field. -/
theorem corollary38_quotientValue_coe {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    L.field.val (G.partition
      (Twins.quotientMatrix (L.matricesK 0) (L.actualTwin_symmetryK hs))
      (Twins.quotientWeight (L.matricesK 0) L.weightsK)) =
      G.partition (Twins.quotientMatrix (L.matrices 0) hs)
        (Twins.quotientWeight (L.matrices 0) L.weights) := by
  rw [← Twins.partition_canonicalQuotient G (L.matricesK 0) L.weightsK
    (L.actualTwin_symmetryK hs)]
  have he := MultiGraph.map_partition L.field.val.toRingHom G (L.matricesK 0) L.weightsK
  exact he.trans (L.corollary38_identity G hs)

/-- Exact real interpretation of the final ordinary unweighted target. -/
theorem actualTwinValue_coe (g : MixedCode) (hg : g.Valid 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    L.field.val (g.evaluate hg (fun _ : Fin 1 => L.actualTwinMatrixK hs)
      (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)) =
      g.evaluate hg (fun _ : Fin 1 => L.actualTwinMatrix hs)
        (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) := by
  simp only [evaluate_homogeneous]
  simpa only [map_one] using MultiGraph.map_partition L.field.val.toRingHom
    (g.toMultiGraph hg) (L.actualTwinMatrixK hs) (fun _ => 1)

private theorem homogeneous_matrices : (fun _ : Fin 1 => L.matricesK 0)=L.matricesK := by
  funext l
  congr 1
  exact (Fin.eq_zero l).symm

private theorem homogeneous_unaries : (fun u : Fin 0 => (Fin.elim0 u : Fin q → L.field))=L.unariesK := by
  funext l
  exact l.elim0

/-- Quotienting alone is a single unchanged-input oracle call. -/
def corollary38_quotient (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    PromisePolyTimeTuringReduction (L.actualQuotientProblem hs) L.problem := by
  have h := quotientReduction L.basis (L.matricesK 0) (L.actualTwin_symmetryK hs) L.weightsK
  rw [L.homogeneous_matrices,L.homogeneous_unaries] at h
  exact h

/-- Deleting the zero class is implemented by the already proved input
component/rooted-restriction machinery; no isolate is silently discarded. -/
def corollary38_weighted (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i) :
    PromisePolyTimeTuringReduction (L.weightedActualTwinProblem hs) L.problem := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have h := weightedReducedReduction L.basis (L.matricesK 0)
    (L.actualTwin_symmetryK hs) L.weightsK hw
  rw [L.homogeneous_matrices,L.homogeneous_unaries] at h
  exact h

/-- Corollary3.8's full real-algebraic reduction, without any algorithm,
availability or hardness assumption. The empty reduced color set is covered
too, so the construction slightly strengthens the stated nonzero-source case. -/
def corollary38 (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i)
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,L.actualTwinMatrix hs i ≠ t • L.actualTwinMatrix hs j) :
    PromisePolyTimeTuringReduction (L.actualTwinProblem hs) L.problem := by
  have h := removeWeightsReduction L.basis (L.matricesK 0)
    (L.actualTwin_symmetryK hs) L.weightsK hw hproj
  rw [L.homogeneous_matrices,L.homogeneous_unaries] at h
  exact h

/-- For zero–one matrices the source row condition is proved automatically.
Arbitrary fixed positive algebraic weights remain on the original oracle. -/
def corollary38_zeroOne (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i) (h01 : ∀ i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    PromisePolyTimeTuringReduction (L.actualTwinProblem hs) L.problem := by
  have h01K : ∀ i j,L.matricesK 0 i j=0 ∨ L.matricesK 0 i j=1 := by
    intro i j
    rcases h01 i j with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have h := zeroOneReduction L.basis (L.matricesK 0)
    (L.actualTwin_symmetryK hs) L.weightsK hw h01K
  rw [L.homogeneous_matrices,L.homogeneous_unaries] at h
  exact h

/-- The unweighted original-oracle specialization of the zero–one result. -/
def corollary38_zeroOne_unweighted (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01 : ∀ i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    PromisePolyTimeTuringReduction (L.actualTwinProblem hs) L.unitWeightProblem := by
  have h01K : ∀ i j,L.matricesK 0 i j=0 ∨ L.matricesK 0 i j=1 := by
    intro i j
    rcases h01 i j with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have h := zeroOneReduction L.basis (L.matricesK 0)
    (L.actualTwin_symmetryK hs) (fun _ => 1) (fun _ => zero_lt_one) h01K
  rw [L.homogeneous_matrices,L.homogeneous_unaries] at h
  exact h

/-- Any hardness reduction to the ordinary quotient lifts by composition to
the weighted original, using the constructed source3.8 reduction. -/
def corollary38_hardnessLift (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i)
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,L.actualTwinMatrix hs i ≠ t • L.actualTwinMatrix hs j)
    (P : PromiseProblem) (r : PromisePolyTimeTuringReduction P (L.actualTwinProblem hs)) :
    PromisePolyTimeTuringReduction P L.problem :=
  r.trans (L.corollary38 hs hw hproj)

def corollary38_zeroOne_hardnessLift (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i) (h01 : ∀ i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1)
    (P : PromiseProblem) (r : PromisePolyTimeTuringReduction P (L.actualTwinProblem hs)) :
    PromisePolyTimeTuringReduction P L.problem :=
  r.trans (L.corollary38_zeroOne hs hw h01)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

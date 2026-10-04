import PlanarHom.Structures
import PlanarHom.RectangularUnitCoreSource

/-! Extracted canonical field/source facts: the unused weighted-form import
is replaced by Structures; all declarations and proof bodies are unchanged.

 Original canonical source-field coordinates for a weighted rectangular
support block. No matrix or answer-codec availability is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteWeightedSourceCanonical
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open RectangularTwinQuotient RectangularWeightedNormNormalization
open Complexity Complexity.MixedCode
variable {p s : ℕ}

def fieldCross (L : RealLanguage (p+s) 1 0) : Matrix (Fin p) (Fin s) L.field :=
  fun i j=>L.matricesK 0 (Fin.castAdd s i) (Fin.natAdd p j)
def fieldLeftWeight (L : RealLanguage (p+s) 1 0) : Fin p→L.field :=
  fun i=>L.weightsK (Fin.castAdd s i)
def fieldRightWeight (L : RealLanguage (p+s) 1 0) : Fin s→L.field :=
  fun j=>L.weightsK (Fin.natAdd p j)

theorem fieldCross_real (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) : realRectangular (fieldCross L)=V := by
  funext i j
  change L.matrices 0 (Fin.castAdd s i) (Fin.natAdd p j)=V i j
  rw [hM]
  simp [block]

theorem fieldMatrix (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) : L.matricesK 0=block (fieldCross L) := by
  funext i j
  apply Subtype.ext
  change L.matrices 0 i j=(block (fieldCross L) i j:ℝ)
  rw [hM]
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
    simp [block,fieldCross,hM]

theorem fieldWeights (L : RealLanguage (p+s) 1 0) :
    L.weightsK=weights (fieldLeftWeight L) (fieldRightWeight L) := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;>
    simp [RectangularBackgroundSourceNormSimulation.weights,fieldLeftWeight,fieldRightWeight]

theorem problem_eq (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) : L.problem=
    evaluationProblem L.basis (fun _:Fin 1=>block (fieldCross L)) (fun u:Fin 0=>u.elim0)
      (weights (fieldLeftWeight L) (fieldRightWeight L)) := by
  have hm : L.matricesK=(fun _:Fin 1=>block (fieldCross L)) := by
    funext l
    have hl : l=0 := Subsingleton.elim _ _
    rw [hl,fieldMatrix L V hM]
  have hu : L.unariesK=(fun u:Fin 0=>u.elim0) := by funext u; exact u.elim0
  change evaluationProblem L.basis L.matricesK L.unariesK L.weightsK=_
  rw [hm,hu,fieldWeights]

theorem cross_rows_injective (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) (hi : Function.Injective (L.matrices 0)) :
    Function.Injective V := by
  intro i j h
  have he : Fin.castAdd s i=Fin.castAdd s j := by
    apply hi
    funext z
    rw [hM,hM]
    refine Fin.addCases (fun z=>?_) (fun z=>?_) z
    · simp [block]
    · simpa [block] using congrFun h z
  apply Fin.ext
  exact congrArg (fun z:Fin (p+s)=>z.val) he

theorem cross_columns_injective (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) (hi : Function.Injective (L.matrices 0)) :
    Function.Injective V.transpose := by
  intro i j h
  have he : Fin.natAdd p i=Fin.natAdd p j := by
    apply hi
    funext z
    rw [hM,hM]
    refine Fin.addCases (fun z=>?_) (fun z=>?_) z
    · simpa [block,Matrix.transpose_apply] using congrFun h z
    · simp [block]
  apply Fin.ext
  have hv := congrArg (fun z:Fin (p+s)=>z.val) he
  change p+i.val=p+j.val at hv
  omega

end PlanarHom.BipartiteWeightedSourceCanonical

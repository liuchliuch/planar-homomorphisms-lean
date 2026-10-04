import PlanarHom.AlgebraicProductInterpolation
import PlanarHom.FieldPresentationReductions
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FixedAlgebraicField
variable {q bt ut dimension : ℕ} (L : RealLanguage q bt ut)
theorem field_le_of_realization (K : IntermediateField ℚ ℝ)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (hM : ∀ l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀ l i,(U l i:ℝ)=L.unaries l i) (hw : ∀ i,(w i:ℝ)=L.weights i) :
    L.field≤K := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨i,rfl⟩
  rcases i with p|p
  · change L.matrices p.1 p.2.1 p.2.2∈K
    rw [←hM]
    exact (M p.1 p.2.1 p.2.2).property
  · rcases p with p|p
    · change L.unaries p.1 p.2∈K
      rw [←hU]
      exact (U p.1 p.2).property
    · rcases p with p|p
      · change L.weights p∈K
        rw [←hw]
        exact (w p).property
      · exact p.elim0
def presentationDescentReduction (K : IntermediateField ℚ ℝ)
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (hM : ∀ l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀ l i,(U l i:ℝ)=L.unaries l i) (hw : ∀ i,(w i:ℝ)=L.weights i) :
    PromisePolyTimeTuringReduction L.problem (evaluationProblem basis M U w) := by
  let φ := IntermediateField.inclusion (L.field_le_of_realization K M U w hM hU hw)
  have hm : (fun l i j=>φ (L.matricesK l i j))=M := by
    funext l i j
    exact Subtype.ext (hM l i j).symm
  have hu : (fun l i=>φ (L.unariesK l i))=U := by
    funext l i
    exact Subtype.ext (hU l i).symm
  have hwp : (fun i=>φ (L.weightsK i))=w := by
    funext i
    exact Subtype.ext (hw i).symm
  have r := fieldDescentReduction L.basis basis φ L.matricesK L.unariesK L.weightsK
  simpa only [hm,hu,hwp] using r
def presentationMapReduction (K : IntermediateField ℚ ℝ)
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (hM : ∀ l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀ l i,(U l i:ℝ)=L.unaries l i) (hw : ∀ i,(w i:ℝ)=L.weights i) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U w) L.problem := by
  let φ := IntermediateField.inclusion (L.field_le_of_realization K M U w hM hU hw)
  have hm : (fun l i j=>φ (L.matricesK l i j))=M := by
    funext l i j
    exact Subtype.ext (hM l i j).symm
  have hu : (fun l i=>φ (L.unariesK l i))=U := by
    funext l i
    exact Subtype.ext (hU l i).symm
  have hwp : (fun i=>φ (L.weightsK i))=w := by
    funext i
    exact Subtype.ext (hw i).symm
  have r := fieldMapReduction L.basis basis φ L.matricesK L.unariesK L.weightsK
  simpa only [hm,hu,hwp] using r
end PlanarHom.AlgebraicProductInterpolation.RealLanguage

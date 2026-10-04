import PlanarHom.RationalVariableEvaluation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! NEW range theorem for the actual rational-variable evaluation embedding. -/
noncomputable section
open scoped Polynomial
namespace PlanarHom.RationalVariableBasis
variable {F E:Type*} [Field F] [Field E] [Algebra F E]

 def evaluateAlgHom (y:E) (hy:Transcendental F y) : FractionRing F[X]→ₐ[F]E where
  __:=evaluate y hy
  commutes':=evaluate_coefficient y hy

 theorem evaluate_fieldRange (y:E) (hy:Transcendental F y) :
    (evaluateAlgHom y hy).fieldRange=IntermediateField.adjoin F {y} := by
  apply IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq (g:=Polynomial.aeval y)
  · apply RingHom.ext
    intro p
    exact evaluate_polynomial y hy p
  · exact (Algebra.adjoin_singleton_eq_range_aeval F y).symm

 def evaluateEquiv (y:E) (hy:Transcendental F y) :
    FractionRing F[X]≃+*IntermediateField.adjoin F {y} :=
  ((AlgEquiv.ofInjectiveField (evaluateAlgHom y hy)).trans
    (IntermediateField.equivOfEq (evaluate_fieldRange y hy))).toRingEquiv

 theorem evaluateEquiv_coe (y:E) (hy:Transcendental F y) (z:FractionRing F[X]) :
    (evaluateEquiv y hy z:E)=evaluate y hy z := by
  rfl

 theorem evaluateEquiv_coefficient (y:E) (hy:Transcendental F y) (r:F) :
    (evaluateEquiv y hy (algebraMap F (FractionRing F[X]) r):E)=algebraMap F E r := by
  rw [evaluateEquiv_coe,evaluate_coefficient]

end PlanarHom.RationalVariableBasis

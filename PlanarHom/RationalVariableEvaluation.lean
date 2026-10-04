import PlanarHom.RationalVariableBasis
import Mathlib.RingTheory.Algebraic.Basic

/-! NEW universal embedding of the one-variable rational-function field at
an actual transcendental element. It fixes all coefficients and preserves the
literal extended basis vectors. -/
noncomputable section
open scoped Polynomial
namespace PlanarHom.RationalVariableBasis
variable {F E:Type*} [Field F] [Field E] [Algebra F E]

 def evaluate (y:E) (hy:Transcendental F y) : FractionRing F[X]→+*E :=
  IsFractionRing.lift (A:=F[X]) (K:=FractionRing F[X]) (g:=(Polynomial.aeval y).toRingHom) (transcendental_iff_injective.mp hy)

 theorem evaluate_polynomial (y:E) (hy:Transcendental F y) (p:F[X]) :
    evaluate y hy (algebraMap F[X] (FractionRing F[X]) p)=Polynomial.aeval y p :=
  IsFractionRing.lift_algebraMap (A:=F[X]) (K:=FractionRing F[X]) _ p

 @[simp] theorem evaluate_coefficient (y:E) (hy:Transcendental F y) (r:F) :
    evaluate y hy (algebraMap F (FractionRing F[X]) r)=algebraMap F E r := by
  change evaluate y hy (algebraMap F[X] (FractionRing F[X]) (Polynomial.C r))=_
  rw [evaluate_polynomial,Polynomial.aeval_C]

 @[simp] theorem evaluate_variable (y:E) (hy:Transcendental F y) :
    evaluate y hy (algebraMap F[X] (FractionRing F[X]) Polynomial.X)=y := by
  rw [evaluate_polynomial,Polynomial.aeval_X]

 theorem evaluate_injective (y:E) (hy:Transcendental F y) : Function.Injective (evaluate y hy) :=
  (evaluate y hy).injective

attribute [local instance] Polynomial.algebra FractionRing.liftAlgebra
variable {K ι:Type*} [Field K] [Algebra K F] [Algebra.IsAlgebraic K F]

 theorem evaluate_basis (b:Module.Basis ι K F) (y:E) (hy:Transcendental F y) (i:ι) :
    evaluate y hy (basis b i)=algebraMap F E (b i) := by
  rw [basis_apply,evaluate_coefficient]

end PlanarHom.RationalVariableBasis

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.FieldTheory.RatFunc.Basic

/-! NEW preservation of the literal finite algebraic basis after adjoining
one transcendental variable. The basis is constructed from the polynomial
pushout and fraction localization, not supplied as a compatibility premise. -/
noncomputable section
open scoped Polynomial TensorProduct
namespace PlanarHom.RationalVariableBasis
attribute [local instance] Polynomial.algebra FractionRing.liftAlgebra
variable {K F ι:Type*} [Field K] [Field F] [Algebra K F] [Algebra.IsAlgebraic K F]

 def basis (b:Module.Basis ι K F) :
    Module.Basis ι (FractionRing K[X]) (FractionRing F[X]) :=
  (Algebra.TensorProduct.basis (FractionRing K[X]) b).map
    (Algebra.IsPushout.equiv K (FractionRing K[X]) F (FractionRing F[X])).toLinearEquiv

 @[simp] theorem basis_apply (b:Module.Basis ι K F) (i:ι) :
    basis b i=algebraMap F (FractionRing F[X]) (b i) := by
  simp only [basis,Module.Basis.map_apply,Algebra.TensorProduct.basis_apply,
    AlgEquiv.toLinearEquiv_apply,Algebra.IsPushout.equiv_tmul,map_one,one_mul]

 theorem scalar (r:K) :
    algebraMap F (FractionRing F[X]) (algebraMap K F r)=
      algebraMap (FractionRing K[X]) (FractionRing F[X])
        (algebraMap K (FractionRing K[X]) r) := by
  rw [←IsScalarTower.algebraMap_apply K F (FractionRing F[X]),
    ←IsScalarTower.algebraMap_apply K (FractionRing K[X]) (FractionRing F[X])]

end PlanarHom.RationalVariableBasis

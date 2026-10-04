import PlanarHom.FractionPolynomialTower
import PlanarHom.RationalVariableEvaluation
import PlanarHom.FixedRealCoordinateDescent

/-! NEW exact one-variable compatibility for the prescribed iterated dense
rational-function codec. The upper algebra and basis are constructed, and the
scalar inclusion is the literal inclusion used by coordinate descent. -/
noncomputable section
open scoped Polynomial
namespace PlanarHom.DenseVariableBasis
open DensePolynomial
attribute [local instance] Polynomial.algebra

 def scalarEquiv (d:ℕ) : RationalFunction (d+1)≃+*FractionRing (RationalFunction d)[X] :=
  FractionPolynomialTower.equiv (Poly d)

 theorem scalarEquiv_inclusion (d:ℕ) (r:RationalFunction d) :
    scalarEquiv d (DenseOuterVariableDescent.inclusion d r)=
      algebraMap (RationalFunction d) (FractionRing (RationalFunction d)[X]) r :=
  FractionPolynomialTower.equiv_baseInclusion (Poly d) r

 def fractionAlgebra (d:ℕ) (F:Type) [Field F] [Algebra (RationalFunction d) F] :
    Algebra (FractionRing (RationalFunction d)[X]) (FractionRing F[X]) :=
  FractionRing.liftAlgebra ((RationalFunction d)[X]) (FractionRing F[X])
attribute [local instance] fractionAlgebra

 def extensionAlgebra (d:ℕ) (F:Type) [Field F] [Algebra (RationalFunction d) F] :
    Algebra (RationalFunction (d+1)) (FractionRing F[X]) :=
  ((algebraMap (FractionRing (RationalFunction d)[X]) (FractionRing F[X])).comp
    (scalarEquiv d).toRingHom).toAlgebra

variable {d e:ℕ} {F:Type} [Field F] [Algebra (RationalFunction d) F]
local instance : Algebra (RationalFunction (d+1)) (FractionRing F[X]):=extensionAlgebra d F

 def upperBasis (lower:Module.Basis (Fin e) (RationalFunction d) F) :
    Module.Basis (Fin e) (RationalFunction (d+1)) (FractionRing F[X]) := by
  letI:Module.Finite (RationalFunction d) F:=Module.Finite.of_basis lower
  exact (RationalVariableBasis.basis lower).mapCoeffs (scalarEquiv d).symm (fun c x=>by
    change ((algebraMap (FractionRing (RationalFunction d)[X]) (FractionRing F[X]))
      (scalarEquiv d ((scalarEquiv d).symm c)))*x=_
    rw [RingEquiv.apply_symm_apply]
    rfl)

 @[simp] theorem upperBasis_apply (lower:Module.Basis (Fin e) (RationalFunction d) F) (i:Fin e) :
    upperBasis lower i=algebraMap F (FractionRing F[X]) (lower i) := by
  simp only [upperBasis,Module.Basis.mapCoeffs_apply,RationalVariableBasis.basis_apply]

 theorem compatible (lower:Module.Basis (Fin e) (RationalFunction d) F) :
    FixedRealCoordinateDescent.Compatible lower (upperBasis lower)
      (algebraMap F (FractionRing F[X])) where
  scalar r:=by
    letI:Module.Finite (RationalFunction d) F:=Module.Finite.of_basis lower
    change algebraMap F (FractionRing F[X]) (algebraMap (RationalFunction d) F r)=
      algebraMap (FractionRing (RationalFunction d)[X]) (FractionRing F[X])
        (scalarEquiv d (DenseOuterVariableDescent.inclusion d r))
    rw [scalarEquiv_inclusion]
    exact RationalVariableBasis.scalar (K:=RationalFunction d) (F:=F) r
  basis i:=(upperBasis_apply lower i).symm

 theorem evaluate_upperBasis {E:Type} [Field E] [Algebra F E]
    (lower:Module.Basis (Fin e) (RationalFunction d) F) (y:E) (hy:Transcendental F y) (i:Fin e) :
    RationalVariableBasis.evaluate y hy (upperBasis lower i)=algebraMap F E (lower i) := by
  rw [upperBasis_apply,RationalVariableBasis.evaluate_coefficient]

end PlanarHom.DenseVariableBasis

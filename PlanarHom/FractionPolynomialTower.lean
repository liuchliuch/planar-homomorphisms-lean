import PlanarHom.RationalVariableBasis
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Algebra

/-! NEW exact fraction-field interchange Frac(R[Y]) ≃ Frac(Frac(R)[Y]),
with explicit coefficient inclusion compatibility. -/
noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PlanarHom.FractionPolynomialTower
attribute [local instance] Polynomial.algebra
variable (R:Type*) [CommRing R] [IsDomain R]

 def polynomialLift : (FractionRing R)[X]→+*FractionRing R[X] := by
  letI:=Polynomial.isLocalization R⁰ (FractionRing R)
  apply IsLocalization.lift (M:=R⁰.map (Polynomial.C:R→+*R[X]))
    (S:=(FractionRing R)[X]) (g:=algebraMap R[X] (FractionRing R[X]))
  intro y
  apply isUnit_iff_ne_zero.mpr
  have hy:(y:R[X])≠0:=by
    obtain ⟨r,hr,he⟩:=y.property
    rw [←he]
    exact Polynomial.C_ne_zero.mpr (nonZeroDivisors.ne_zero hr)
  exact fun h=>hy ((IsFractionRing.injective R[X] (FractionRing R[X])) (by simpa using h))

 theorem polynomialLift_map (p:R[X]) :
    polynomialLift R (p.map (algebraMap R (FractionRing R)))=algebraMap R[X] (FractionRing R[X]) p := by
  letI:=Polynomial.isLocalization R⁰ (FractionRing R)
  unfold polynomialLift
  exact IsLocalization.lift_eq (M:=R⁰.map (Polynomial.C:R→+*R[X]))
    (S:=(FractionRing R)[X]) _ p

 def localizedAlgebra : Algebra (FractionRing R)[X] (FractionRing R[X]) :=
  (polynomialLift R).toAlgebra
attribute [local instance] localizedAlgebra

 instance localizedTower : IsScalarTower R[X] (FractionRing R)[X] (FractionRing R[X]) :=
  IsScalarTower.of_algebraMap_eq (fun p=>(polynomialLift_map R p).symm)

 def localizedFractionRing : IsFractionRing (FractionRing R)[X] (FractionRing R[X]) := by
  letI:=Polynomial.isLocalization R⁰ (FractionRing R)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (R⁰.map (Polynomial.C:R→+*R[X])) (FractionRing R)[X] (FractionRing R[X])
attribute [local instance] localizedFractionRing

 def equiv : FractionRing R[X]≃+*FractionRing (FractionRing R)[X] :=
  (IsLocalization.algEquiv ((FractionRing R)[X])⁰ (FractionRing R[X])
    (FractionRing (FractionRing R)[X])).toRingEquiv

 theorem equiv_map (p:R[X]) :
    equiv R (algebraMap R[X] (FractionRing R[X]) p)=
      algebraMap (FractionRing R)[X] (FractionRing (FractionRing R)[X])
        (p.map (algebraMap R (FractionRing R))) := by
  rw [←polynomialLift_map]
  exact (IsLocalization.algEquiv ((FractionRing R)[X])⁰ (FractionRing R[X])
    (FractionRing (FractionRing R)[X])).commutes _

 def baseInclusion : FractionRing R→+*FractionRing R[X] :=
  IsFractionRing.lift (g:=(algebraMap R[X] (FractionRing R[X])).comp Polynomial.C)
    ((IsFractionRing.injective R[X] (FractionRing R[X])).comp Polynomial.C_injective)

 theorem baseInclusion_algebraMap (r:R) :
    baseInclusion R (algebraMap R (FractionRing R) r)=
      algebraMap R[X] (FractionRing R[X]) (Polynomial.C r) := by
  unfold baseInclusion
  exact IsFractionRing.lift_algebraMap
    (g:=(algebraMap R[X] (FractionRing R[X])).comp (Polynomial.C:R→+*R[X])) _ r

 theorem equiv_baseInclusion (r:FractionRing R) :
    equiv R (baseInclusion R r)=algebraMap (FractionRing R) (FractionRing (FractionRing R)[X]) r := by
  have hh : (equiv R).toRingHom.comp (baseInclusion R)=
      algebraMap (FractionRing R) (FractionRing (FractionRing R)[X]) := by
    apply IsLocalization.ringHom_ext R⁰
    ext r
    change equiv R (baseInclusion R (algebraMap R (FractionRing R) r))=_
    rw [baseInclusion_algebraMap,equiv_map,Polynomial.map_C]
    rfl
  exact RingHom.congr_fun hh r

end PlanarHom.FractionPolynomialTower

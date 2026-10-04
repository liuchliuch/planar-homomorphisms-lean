import PlanarHom.DenseVariableBasisCompatibility
import PlanarHom.FixedRealVariableTowerDescent

/-! NEW finite tower of genuine rational-variable extensions with exactly the
original finite basis images and the literal iterated scalar inclusion. -/
noncomputable section
open scoped Polynomial
namespace PlanarHom.DenseVariableBasis
open DensePolynomial
attribute [local instance] Polynomial.algebra

 structure FieldStage where
  Carrier:Type
  field:Field Carrier
 instance : CoeSort FieldStage Type:=⟨FieldStage.Carrier⟩
 instance (S:FieldStage) : Field S:=S.field

 def stage (F:Type) [Field F] : ℕ→FieldStage
  | 0=>⟨F,inferInstance⟩
  | b+1=>⟨FractionRing (stage F b)[X],inferInstance⟩

 abbrev Tower (F:Type) [Field F] (b:ℕ) : Type:=stage F b

 def towerAlgebra (c:ℕ) (F:Type) [Field F] [Algebra (RationalFunction c) F] :
    (b:ℕ)→Algebra (RationalFunction (c+b)) (Tower F b)
  | 0=>inferInstanceAs (Algebra (RationalFunction c) F)
  | b+1=>letI:=towerAlgebra c F b;extensionAlgebra (c+b) (Tower F b)
attribute [local instance] towerAlgebra

 def embedding (F:Type) [Field F] : (b:ℕ)→F→+*Tower F b
  | 0=>RingHom.id F
  | b+1=>(algebraMap (Tower F b) (FractionRing (Tower F b)[X])).comp (embedding F b)

variable {c e:ℕ} {F:Type} [Field F] [Algebra (RationalFunction c) F]

 def towerBasis (lower:Module.Basis (Fin e) (RationalFunction c) F) :
    (b:ℕ)→Module.Basis (Fin e) (RationalFunction (c+b)) (Tower F b)
  | 0=>lower
  | b+1=>by
    letI:=towerAlgebra c F b
    exact upperBasis (d:=c+b) (towerBasis lower b)

 theorem towerBasis_apply (lower:Module.Basis (Fin e) (RationalFunction c) F) (b:ℕ) (i:Fin e) :
    towerBasis lower b i=embedding F b (lower i) := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    letI:=towerAlgebra c F b
    change upperBasis (d:=c+b) (towerBasis lower b) i=_
    rw [upperBasis_apply,ih]
    rfl

 theorem tower_compatible (lower:Module.Basis (Fin e) (RationalFunction c) F) (b:ℕ) :
    FixedRealVariableTowerDescent.Compatible lower (towerBasis lower b) (embedding F b) := by
  refine ⟨?_,fun i=>(towerBasis_apply lower b i).symm⟩
  intro r
  induction b with
  | zero=>rfl
  | succ b ih=>
    letI:=towerAlgebra c F b
    change algebraMap (Tower F b) (FractionRing (Tower F b)[X])
      (embedding F b (algebraMap (RationalFunction c) F r))=_
    rw [ih]
    letI:=extensionAlgebra (c+b) (Tower F b)
    exact (compatible (d:=c+b) (towerBasis lower b)).scalar (FixedRealVariableTowerDescent.inclusion c b r)

end PlanarHom.DenseVariableBasis

import PlanarHom.RepresentedRootRestriction
import PlanarHom.FixedRealExtensionPresentation

/-! Concrete fixed-real homogeneous root restriction in the actual shared-
denominator extension presentation. The only basis is over Q(X₁,…,Xₙ), as
specified by the Appendix model; no finite-dimensionality over Q is assumed.
All representative arithmetic and the charged oracle machine are constructed. -/
noncomputable section
namespace PlanarHom.FixedRealRootRestriction
open DensePolynomial RepresentedBit
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def arithmetic (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    AddMulMachines (FixedRealExtension.presentation basis) where
  add:=fun p=>FixedRealExtension.add n p.1 p.2
  mul:=fun p=>FixedRealExtension.mul (FixedRealExtension.multiplicationTable basis) p.1 p.2
  fp_add:=FixedRealExtension.fp_add n e
  fp_mul:=FixedRealExtension.fp_mul n e (FixedRealExtension.multiplicationTable basis)
  add_valid:=FixedRealExtension.add_valid
  add_value:=FixedRealExtension.value_add basis
  mul_valid:=FixedRealExtension.mul_valid _
  mul_value:=fun a b _ _=>FixedRealExtension.value_mul _ basis
    (FixedRealExtension.multiplicationTable_realizes basis) a b

variable [LinearOrder K] [IsStrictOrderedRing K] {C:Type} [Fintype C]

def corollaryA2_root (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Matrix C C K) (w:C→K) (hw:∀i,0 < w i) (X:Set C) :
    Reduction (RepresentedRootRestriction.rootProblem (FixedRealExtension.presentation basis) M w X)
      (RepresentedRootRestriction.sourceProblem (FixedRealExtension.presentation basis) M w) :=
  RepresentedRootRestriction.rootReduction (FixedRealExtension.presentation basis) (arithmetic basis) M w hw X

end PlanarHom.FixedRealRootRestriction

import PlanarHom.FixedRealWeightPowersJoint

/-! NEW construction of the fixed rational-power overfield and its actual
represented joint reductions back to the original prescribed oracle. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity FixedRealExtension RepresentedBit FixedRealMixedInterpolation
open RelativeWeightedSpectralField
variable {n e q bt ut s:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

/-- Fixed presentation data produced by the actual finite root extension. -/
structure PowerModel (w:Fin q→F) (r:Fin s→ℚ) where
  Carrier : Type
  [field : Field Carrier]
  [baseAlgebra : Algebra (RationalFunction n) Carrier]
  [realAlgebra : Algebra Carrier ℝ]
  inclusion : F→ₐ[RationalFunction n] Carrier
  real_inclusion : ∀x,algebraMap Carrier ℝ (inclusion x)=algebraMap F ℝ x
  dimension : ℕ
  basis : Module.Basis (Fin dimension) (RationalFunction n) Carrier
  powers : Fin s→Fin q→Carrier
  powers_real : ∀j i,algebraMap Carrier ℝ (powers j i)=realWeights w i^(r j:ℝ)
attribute [instance] PowerModel.field PowerModel.baseAlgebra PowerModel.realAlgebra

def powerModel (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (w:Fin q→F) (hw:∀i,0<realWeights w i) (r:Fin s→ℚ) : PowerModel (n:=n) w r := by
  let E:=RelativeRationalPowerField.field w r
  letI : Algebra (RationalFunction n) E :=
    ((algebraMap F E).comp (algebraMap (RationalFunction n) F)).toAlgebra
  letI : IsScalarTower (RationalFunction n) F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional F E := RelativeRationalPowerField.finiteDimensional w hw r
  letI : FiniteDimensional (RationalFunction n) F := Module.Finite.of_basis basis
  letI : FiniteDimensional (RationalFunction n) E := FiniteDimensional.trans (RationalFunction n) F E
  exact { Carrier:=E
          field:=inferInstance
          baseAlgebra:=inferInstance
          realAlgebra:=inferInstance
          inclusion:=IsScalarTower.toAlgHom (RationalFunction n) F E
          real_inclusion:=fun _=>rfl
          dimension:=Module.finrank (RationalFunction n) E
          basis:=Module.finBasis (RationalFunction n) E
          powers:=RelativeRationalPowerField.powered w r
          powers_real:=fun _ _=>rfl }


variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

/-- The roots are constructed from the source weights, while oracle answers
remain in the original source presentation. All supplied mixed labels survive. -/
def constructedPowers_joint (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (r:Fin s→ℚ) :
    let P:=powerModel basis w hw r
    Reduction (problem P.basis
      (powerMatrices (fun l i j=>P.inclusion (M l i j)) (fun i=>P.inclusion (w i)) P.powers)
      (powerUnaries (fun l i=>P.inclusion (U l i)) P.powers) (fun _=>1)) (problem basis M U w) := by
  dsimp only
  let P:=powerModel basis w hw r
  let ME:=fun l i j=>P.inclusion (M l i j)
  let UE:=fun l i=>P.inclusion (U l i)
  let wE:=fun i=>P.inclusion (w i)
  have hm:realMatrix (ME old)=realMatrix (M old) := by
    funext i j
    exact P.real_inclusion _
  have hwE:realWeights wE=realWeights w := by
    funext i
    exact P.real_inclusion _
  have first:=powersUnary_unit_joint P.basis ME UE wE old
    (by simpa only [hm] using hs) (by simpa only [hwE] using hw)
    (by simpa only [hm] using hnonzero) (by simpa only [hm] using hproj) r P.powers
    (by intro j i; rw [hwE]; exact P.powers_real j i)
  exact first.trans (FixedRealValueMapReduction.fieldMap basis P.basis P.inclusion M U w)

end PlanarHom.FixedRealWeightRemoval

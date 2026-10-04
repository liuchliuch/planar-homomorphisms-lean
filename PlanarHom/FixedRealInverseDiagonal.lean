import PlanarHom.RelativeWeightedSpectralField
import PlanarHom.FixedRealWeightedSpectralReduction
import PlanarHom.FixedRealValueMapReduction
import PlanarHom.RepresentedReductionComposition

/-! NEW A.8 inverse-diagonal availability in the original prescribed source
presentation. The actual spectral extension is finite over the source field;
its interpolation uses a proved RF(n)-basis and returns via normalized trace. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation ProductCompatibility FiniteLanguageAliases
open RelativeWeightedSpectralField
variable {n e q bt ut:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

def inverseDiagonalAppendReduction (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hA:(realMatrix (M old)).PosDef) (hw:∀i,0<realWeights w i) :
    Reduction (problem basis (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w)
      (problem basis M U w) := by
  let A:=M old
  let E:=field A w
  letI : Algebra (RationalFunction n) E :=
    ((algebraMap F E).comp (algebraMap (RationalFunction n) F)).toAlgebra
  letI : IsScalarTower (RationalFunction n) F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional F E := finiteDimensional A hA w hw
  letI : FiniteDimensional (RationalFunction n) F := Module.Finite.of_basis basis
  letI : FiniteDimensional (RationalFunction n) E := FiniteDimensional.trans (RationalFunction n) F E
  letI : CharZero F := ((algebraMap F ℝ).charZero)
  let bE:=Module.finBasis (RationalFunction n) E
  let φ:F→ₐ[RationalFunction n] E:=IsScalarTower.toAlgHom (RationalFunction n) F E
  let ME:Fin bt→Matrix (Fin q) (Fin q) E:=fun l i j=>φ (M l i j)
  let UE:Fin ut→Fin q→E:=fun l i=>φ (U l i)
  let wE:Fin q→E:=fun i=>φ (w i)
  have hzero:∀i,scalar A w i=0→(1:E)=0 := by
    intro i hi
    have hr:RealSpectralInterpolation.scalar (spectralMatrix A w) i=0:=
      congrArg (fun x:E=>(x:ℝ)) hi
    exact ((ne_of_gt (RealSpectralInterpolation.scalar_pos _
      (PositiveWeightRemoval.weightedConjugate_posDef (realMatrix A) hA (realWeights w) hw) i)) hr).elim
  have hc:Compatible (scalar A w) (fun _=>(1:E)) := by
    intro xs ys _ _ _ _
    simp
  let first:=FixedRealWeightedGadgets.spectralAppendReduction bE ME UE wE old
    (projector A w) (scalar A w) (fun _=>1) (chain A hA w hw) hzero hc
  have hsum:(∑i,(1:E) • projector A w i)=
      (Matrix.diagonal (fun i=>(w i)⁻¹)).map φ := by
    simpa only [one_smul] using projector_sum A hA w hw
  have happ:(fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j))=
      appendOne ME ((Matrix.diagonal (fun i=>(w i)⁻¹)).map φ) := by
    funext l
    refine Fin.lastCases ?_ (fun k=>?_) l
    · simp only [appendOne_aux]
      rfl
    · change (fun i j=>φ (appendOne M _ (Fin.castAdd 1 k) i j))=appendOne ME _ (Fin.castAdd 1 k)
      simp only [appendOne_old]
      rfl
  have second:=FixedRealValueMapReduction.fieldMap basis bE φ M U w
  have third:=FixedRealValueMapReduction.fieldDescent basis bE
    (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w
  change Reduction (problem bE (appendOne ME (∑i,(1:E) • projector A w i)) UE wE)
    (problem bE ME UE wE) at first
  rw [hsum] at first
  change Reduction _ (problem bE
    (fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)) UE wE) at third
  rw [happ] at third
  exact third.trans (first.trans second)

end PlanarHom.FixedRealWeightRemoval

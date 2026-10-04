import PlanarHom.FixedRealGaugeMomentReduction
import PlanarHom.FixedRealWeightPowerExtension
import PlanarHom.PositiveUnaryRationalPowers
import PlanarHom.Normalization

/-! NEW: actual fixed-real diagonal normalization and every fixed integral
vertex moment. The inverse square roots are constructed in one fixed finite
extension, unary powers use the joint interpolation machine, and endpoints and
all vertices receive their literal original unary occurrences. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealPositiveNormalization
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit
open FixedRealMixedInterpolation FixedRealWeightRemoval FiniteLanguageAliases
open ProductCompatibility EndpointUnarySource RelativeWeightedSpectralField
variable {d e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction d) K] [Algebra K ℝ]
variable (basis : Module.Basis (Fin e) (RationalFunction d) K)

def unaryPowerReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin u)
    (hv : ∀ i, 0 < algebraMap K ℝ (U old i)) (r : ℚ) (v : Fin q → K)
    (hr : ∀ i, algebraMap K ℝ (v i) = (algebraMap K ℝ (U old i)) ^ (r : ℝ)) :
    Reduction (problem basis M (appendOne U v) w) (problem basis M U w) := by
  apply unaryAppendReduction basis M U w v old
  · intro i hi
    exact False.elim ((ne_of_gt (hv i)) (by rw [hi,map_zero]))
  · apply hasProductMaps_of_compatible
    apply compatible_of_field_embedding (algebraMap K ℝ)
    have he : (fun i => algebraMap K ℝ (v i)) =
        (fun i => algebraMap K ℝ (U old i) ^ (r : ℝ)) := funext hr
    rw [he]
    exact PositiveUnaryRationalPowers.compatible_real_rpow _ hv _

def inverseModel (M : Fin b → Matrix (Fin q) (Fin q) K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) :=
  powerModel basis (fun i => M old i i) hpos (fun _ : Fin 1 => (-1 / 2 : ℚ))

def normalizedMatrix (M : Fin b → Matrix (Fin q) (Fin q) K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) :=
  let P := inverseModel basis M old hpos
  unaryGauge (fun i j => P.inclusion (M old i j)) (P.powers 0)

theorem inverseModel_power_real (M : Fin b → Matrix (Fin q) (Fin q) K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) (i : Fin q) :
    let P := inverseModel basis M old hpos
    algebraMap P.Carrier ℝ (P.powers 0 i) = (Real.sqrt (algebraMap K ℝ (M old i i)))⁻¹ := by
  dsimp only
  rw [(inverseModel basis M old hpos).powers_real]
  change algebraMap K ℝ (M old i i) ^ ((-1 / 2 : ℚ) : ℝ) = _
  have he : ((-1 / 2 : ℚ) : ℝ) = -(1 / (2 : ℝ)) := by norm_num
  rw [he,Real.rpow_neg (hpos i).le,←Real.sqrt_eq_rpow]

theorem normalizedMatrix_real (M : Fin b → Matrix (Fin q) (Fin q) K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) (i j : Fin q) :
    let P := inverseModel basis M old hpos
    algebraMap P.Carrier ℝ (normalizedMatrix basis M old hpos i j) =
      diagonalNormalize (fun i j => algebraMap K ℝ (M old i j)) i j := by
  dsimp only
  simp only [normalizedMatrix,unaryGauge,map_mul,(inverseModel basis M old hpos).real_inclusion,
    inverseModel_power_real]
  simp only [diagonalNormalize,div_eq_mul_inv,mul_inv_rev]
  ring

def inverseUnaryReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) :
    let P := inverseModel basis M old hpos
    Reduction (problem P.basis (fun l i j => P.inclusion (M l i j))
      (appendOne (fun l i => P.inclusion (appendOne U (fun i => M old i i) l i)) (P.powers 0))
      (fun i => P.inclusion (w i))) (problem basis M U w) := by
  dsimp only
  let P := inverseModel basis M old hpos
  let ME := fun l i j => P.inclusion (M l i j)
  let UE := fun l i => P.inclusion (appendOne U (fun i => M old i i) l i)
  let wE := fun i => P.inclusion (w i)
  have first := unaryPowerReduction P.basis ME UE wE (Fin.last u)
    (fun i => by simpa only [UE,appendOne_aux,P.real_inclusion] using hpos i)
    (-1/2) (P.powers 0) (fun i => by
      simpa only [UE,appendOne_aux,P.real_inclusion,realWeights] using P.powers_real 0 i)
  exact first.trans ((FixedRealValueMapReduction.fieldMap basis P.basis P.inclusion M
    (appendOne U (fun i => M old i i)) w).trans (diagonalUnaryAppendReduction basis M U w old))

/-- Discarding fixed companion labels is a literal relabeling of the same graph. -/
def selectedMatrixReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b) :
    Reduction (problem basis (fun _ : Fin 1 => M old) (fun l : Fin 0 => l.elim0) w)
      (problem basis M U w) := by
  have rb := binaryRelabelReduction basis (fun _ : Fin 1 => old) M U w
  have ru := unaryRelabelReduction basis (fun l : Fin 0 => l.elim0) (fun _ : Fin 1 => M old) U w
  have hu : U ∘ (fun l : Fin 0 => l.elim0) = (fun l : Fin 0 => l.elim0) := by
    funext l
    exact l.elim0
  simpa only [hu] using ru.trans rb

/-- A single fixed extension works for every moment order. Each fixed order has
an actual polynomial-time query compiler and represented answer recovery. -/
def normalizedMomentReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (M old i i)) (m : ℕ) :
    let P := inverseModel basis M old hpos
    Reduction (problem P.basis (fun _ : Fin 1 => normalizedMatrix basis M old hpos)
      (fun l : Fin 0 => l.elim0) (fun i => P.inclusion (w i) * P.inclusion (M old i i)^m))
      (problem basis M U w) := by
  dsimp only
  let P := inverseModel basis M old hpos
  let ME := fun l i j => P.inclusion (M l i j)
  let UE := appendOne (fun l i => P.inclusion (appendOne U (fun i => M old i i) l i)) (P.powers 0)
  let wE := fun i => P.inclusion (w i)
  have hroot : UE (Fin.last (u+1)) = P.powers 0 := appendOne_aux _ _
  have hdiag : UE (Fin.castAdd 1 (Fin.last u)) = fun i => P.inclusion (M old i i) := by
    funext i
    simp only [UE,appendOne_old,appendOne_aux]
  have stage := (FixedRealGaugeMoments.gaugeMomentReduction P.basis ME UE wE old
    (Fin.last (u+1)) (Fin.castAdd 1 (Fin.last u)) m).trans
      (inverseUnaryReduction basis M U w old hpos)
  rw [hroot,hdiag] at stage
  have selected := selectedMatrixReduction P.basis
    (appendOne ME (normalizedMatrix basis M old hpos)) UE
    (fun i => wE i * P.inclusion (M old i i)^m) (Fin.last b)
  simpa only [appendOne_aux] using selected.trans stage

end PlanarHom.FixedRealPositiveNormalization

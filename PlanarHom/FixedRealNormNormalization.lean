import PlanarHom.FixedRealPositiveNormalization
import PlanarHom.FixedRealWeightedGadgets
import PlanarHom.RectangularSquareNormSource

/-! NEW: weighted row-norm normalization in the represented model. The norm
unary is the actual two-edge return gadget with its original internal weight.
One fixed root extension supports all moment orders; no availability premise is
assumed and neither side's background is replaced by unit weights. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealNormNormalization
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit
open FixedRealMixedInterpolation FixedRealWeightRemoval FiniteLanguageAliases
open RectangularBackgroundSourceNormSimulation EndpointUnarySource PositiveWeightRemoval
variable {d e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction d) K] [Algebra K ℝ]
variable (basis : Module.Basis (Fin e) (RationalFunction d) K)

def squareNormUnaryReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hs : ∀ i j, M old i j = M old j i) :
    Reduction (problem basis M (appendOne U (squareNorm (M old) w)) w) (problem basis M U w) := by
  let G := gramCoreField (M old) w 1
  have hr := (diagonalUnaryAppendReduction basis (appendOne M G) U w (Fin.last b)).trans
    (FixedRealWeightedGadgets.gramAppendReduction basis M U w old 1)
  simp only [appendOne_aux] at hr
  have hd : (fun i => G i i) = squareNorm (M old) w := by
    funext i
    simp only [G,gramCoreField,pow_one]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,squareNorm]
    apply Finset.sum_congr rfl
    intro j _
    rw [←hs i j]
    ring
  rw [hd] at hr
  have skip :=  binaryRelabelReduction basis (Fin.castAdd 1) (appendOne M G)
    (appendOne U (squareNorm (M old) w)) w
  have hm : (appendOne M G) ∘ Fin.castAdd 1 = M := by
    funext l
    exact appendOne_old _ _ _
  rw [hm] at skip
  exact skip.trans hr

def normModel (M : Fin b → Matrix (Fin q) (Fin q) K) (w : Fin q → K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (squareNorm (M old) w i)) :=
  powerModel basis (squareNorm (M old) w) hpos (fun _ : Fin 1 => (-1/2 : ℚ))

def normalizedMatrix (M : Fin b → Matrix (Fin q) (Fin q) K) (w : Fin q → K) (old : Fin b)
    (hpos : ∀ i, 0 < algebraMap K ℝ (squareNorm (M old) w i)) :=
  let P := normModel basis M w old hpos
  unaryGauge (fun i j => P.inclusion (M old i j)) (P.powers 0)

theorem normModel_power_real (M : Fin b → Matrix (Fin q) (Fin q) K)
    (w : Fin q → K) (old : Fin b) (hpos : ∀ i, 0 < algebraMap K ℝ (squareNorm (M old) w i))
    (i : Fin q) :
    let P := normModel basis M w old hpos
    algebraMap P.Carrier ℝ (P.powers 0 i) =
      (Real.sqrt (algebraMap K ℝ (squareNorm (M old) w i)))⁻¹ := by
  dsimp only
  rw [(normModel basis M w old hpos).powers_real]
  change algebraMap K ℝ (squareNorm (M old) w i) ^ ((-1/2 : ℚ) : ℝ) = _
  have he : ((-1/2 : ℚ) : ℝ) = -(1/(2 : ℝ)) := by norm_num
  rw [he,Real.rpow_neg (hpos i).le,←Real.sqrt_eq_rpow]

def inverseNormUnaryReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hs : ∀ i j, M old i j = M old j i)
    (hpos : ∀ i, 0 < algebraMap K ℝ (squareNorm (M old) w i)) :
    let P := normModel basis M w old hpos
    Reduction (problem P.basis (fun l i j => P.inclusion (M l i j))
      (appendOne (fun l i => P.inclusion (appendOne U (squareNorm (M old) w) l i)) (P.powers 0))
      (fun i => P.inclusion (w i))) (problem basis M U w) := by
  dsimp only
  let P := normModel basis M w old hpos
  let ME := fun l i j => P.inclusion (M l i j)
  let UE := fun l i => P.inclusion (appendOne U (squareNorm (M old) w) l i)
  let wE := fun i => P.inclusion (w i)
  have first := FixedRealPositiveNormalization.unaryPowerReduction P.basis ME UE wE (Fin.last u)
    (fun i => by simpa only [UE,appendOne_aux,P.real_inclusion] using hpos i)
    (-1/2) (P.powers 0) (fun i => by
      simpa only [UE,appendOne_aux,P.real_inclusion,RelativeWeightedSpectralField.realWeights] using P.powers_real 0 i)
  exact first.trans ((FixedRealValueMapReduction.fieldMap basis P.basis P.inclusion M
    (appendOne U (squareNorm (M old) w)) w).trans (squareNormUnaryReduction basis M U w old hs))

def normalizedMomentReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hs : ∀ i j, M old i j = M old j i)
    (hpos : ∀ i, 0 < algebraMap K ℝ (squareNorm (M old) w i)) (m : ℕ) :
    let P := normModel basis M w old hpos
    Reduction (problem P.basis (fun _ : Fin 1 => normalizedMatrix basis M w old hpos)
      (fun l : Fin 0 => l.elim0) (fun i => P.inclusion (w i) * P.inclusion (squareNorm (M old) w i)^m))
      (problem basis M U w) := by
  dsimp only
  let P := normModel basis M w old hpos
  let ME := fun l i j => P.inclusion (M l i j)
  let UE := appendOne (fun l i => P.inclusion (appendOne U (squareNorm (M old) w) l i)) (P.powers 0)
  let wE := fun i => P.inclusion (w i)
  have hroot : UE (Fin.last (u+1)) = P.powers 0 := appendOne_aux _ _
  have hnorm : UE (Fin.castAdd 1 (Fin.last u)) = fun i => P.inclusion (squareNorm (M old) w i) := by
    funext i
    simp only [UE,appendOne_old,appendOne_aux]
  have stage := (FixedRealGaugeMoments.gaugeMomentReduction P.basis ME UE wE old
    (Fin.last (u+1)) (Fin.castAdd 1 (Fin.last u)) m).trans
      (inverseNormUnaryReduction basis M U w old hs hpos)
  rw [hroot,hnorm] at stage
  have selected := FixedRealPositiveNormalization.selectedMatrixReduction P.basis
    (appendOne ME (normalizedMatrix basis M w old hpos)) UE
    (fun i => wE i * P.inclusion (squareNorm (M old) w i)^m) (Fin.last b)
  simpa only [appendOne_aux] using selected.trans stage

end PlanarHom.FixedRealNormNormalization

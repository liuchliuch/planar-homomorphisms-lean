import PlanarHom.SpectralAppendReduction
import PlanarHom.SpectralFieldPresentation
import PlanarHom.RealSpectralProjector

/-! Genuine spectral interpolation in one fixed overfield, with the original
source oracle's supplied basis preserved through an actual answer converter. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralAvailability
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility
open SpectralFieldPresentation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dimension : ℕ}

/-- General spectral-function availability, with all spectral data and matrix
power identities constructed from the actual CFC. -/
def cfcAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (old : Fin bt)
    (hC : (realMatrix (M old)).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ (realMatrix (M old)), IsAlgebraic ℚ (f x))
    (hzero : ∀ i, RealSpectralInterpolation.scalar (realMatrix (M old)) i=0 →
      f (RealSpectralInterpolation.scalar (realMatrix (M old)) i)=0)
    (hcompat : Compatible (RealSpectralInterpolation.scalar (realMatrix (M old)))
      (fun i => f (RealSpectralInterpolation.scalar (realMatrix (M old)) i))) :
    PromisePolyTimeTuringReduction
      (evaluationProblem (basis (M old) hC f hf)
        (appendOne (fun l i j => inclusion (M old) f (M l i j)) (N (M old) f))
        (fun l i => inclusion (M old) f (U l i)) (fun _ => 1))
      (evaluationProblem b₀ M U (fun _ => 1)) := by
  let C := M old
  let φ := inclusion C f
  let bF := basis C hC f hf
  let MF : Fin bt → Matrix (Fin q) (Fin q) (field C f) := fun l i j => φ (M l i j)
  let UF : Fin ut → Fin q → field C f := fun l i => φ (U l i)
  have hp : ∀ n : ℕ, 0<n → MF old ^ n = ∑ i, a C f i ^ n • P C f i := by
    intro n _
    exact sourceMatrix_pow C hC f n
  let first := spectralAppendReduction bF MF UF old (P C f) (a C f) (b C f) hp
    (zero_lift C f hzero) (compatible_lift C f hcompat)
  have second : PromisePolyTimeTuringReduction (evaluationProblem bF MF UF (fun _ => 1))
      (evaluationProblem b₀ M U (fun _ => 1)) := by
    simpa only [map_one] using fieldMapReduction b₀ bF φ M U (fun _ => 1)
  have result := first.trans second
  change PromisePolyTimeTuringReduction (evaluationProblem bF (appendOne MF (N C f)) UF (fun _ => 1)) _
  rw [N_eq_sum C f]
  exact result

def rangeFunction (x : ℝ) : ℝ := if 0<x then 1 else 0

theorem rangeFunction_algebraic (A : Matrix (Fin q) (Fin q) ℝ) :
    ∀ x ∈ spectrum ℝ A, IsAlgebraic ℚ (rangeFunction x) := by
  intro x _
  unfold rangeFunction
  split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero

theorem rangeFunction_zero (A : Matrix (Fin q) (Fin q) ℝ) :
    ∀ i, RealSpectralInterpolation.scalar A i=0 → rangeFunction (RealSpectralInterpolation.scalar A i)=0 := by
  intro i h
  simp [rangeFunction,h]

theorem rangeFunction_compatible (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosSemidef) :
    Compatible (RealSpectralInterpolation.scalar A) (fun i => rangeFunction (RealSpectralInterpolation.scalar A i)) := by
  have he : (fun i => rangeFunction (RealSpectralInterpolation.scalar A i)) =
      (fun i => if RealSpectralInterpolation.scalar A i=0 then (0 : ℝ) else 1) :=
    funext (RealSpectralInterpolation.range_coefficients A hA)
  rw [he]
  exact RealSpectralInterpolation.compatible_nonzero_indicator _

/-- Actual PSD range-projector availability, including the zero source. -/
def rangeAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (old : Fin bt)
    (hC : (realMatrix (M old)).PosSemidef) :=
  cfcAppendOverfieldReduction b₀ M U old hC.1 rangeFunction (rangeFunction_algebraic _)
    (rangeFunction_zero _) (rangeFunction_compatible _ hC)

theorem powerFunction_algebraic (C : Matrix (Fin q) (Fin q) K₀)
    (hC : (realMatrix C).PosDef) (r : ℚ) :
    ∀ x ∈ spectrum ℝ (realMatrix C), IsAlgebraic ℚ (x ^ (r : ℝ)) := by
  intro x hx
  obtain ⟨i,rfl⟩ := RealSpectralInterpolation.scalar_surjective (realMatrix C) x hx
  exact PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat
    (RealSpectralInterpolation.scalar_pos _ hC i)
    (AlgebraicSpectralData.isAlgebraic_of_mem_spectrum _ (realMatrix_isAlgebraic C)
      (RealSpectralInterpolation.scalar_mem _ i)) r

theorem powerFunction_zero (C : Matrix (Fin q) (Fin q) K₀)
    (hC : (realMatrix C).PosDef) (r : ℚ) :
    ∀ i, RealSpectralInterpolation.scalar (realMatrix C) i=0 →
      RealSpectralInterpolation.scalar (realMatrix C) i ^ (r : ℝ)=0 := by
  intro i h
  exact ((ne_of_gt (RealSpectralInterpolation.scalar_pos _ hC i)) h).elim

/-- Every fixed rational power, with zero and negative exponents permitted. -/
def rationalPowerAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (old : Fin bt)
    (hC : (realMatrix (M old)).PosDef) (r : ℚ) :=
  cfcAppendOverfieldReduction b₀ M U old hC.1 (fun x => x ^ (r : ℝ))
    (powerFunction_algebraic _ hC r) (powerFunction_zero _ hC r)
    (PositiveUnaryRationalPowers.compatible_real_rpow _ (RealSpectralInterpolation.scalar_pos _ hC) r)

end PlanarHom.SpectralAvailability

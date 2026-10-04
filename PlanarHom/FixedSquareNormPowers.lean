import PlanarHom.FixedSquareNormSource
import PlanarHom.PositiveUnaryPowerJointAvailability

/-!
# Fixed rational square-norm unaries from the original source

NEW reconstruction. The original source field is retained as a subfield of one
fixed finite extension. Interpolation and answer descent are supplied by actual
baseline programs; no oracle availability is accepted as an input assumption.
-/
noncomputable section
open Classical
namespace PlanarHom.FixedSquareNormSource
open Complexity Complexity.MixedCode FiniteLanguageAliases
open RectangularBackgroundSourceNormSimulation PositiveUnaryRationalPowers

variable {K₀ : IntermediateField ℚ ℝ} {q d bt ut : ℕ}

/-- Every fixed rational power of a positive conditional square norm, jointly
with the original constraints and the original square-norm unary. -/
theorem exists_squareNorm_rational_unary
    (basis : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (w : Fin q → K₀) (old : Fin bt) (hs : ∀ i j, M old i j = M old j i)
    (hpos : ∀ i, 0 < ((squareNorm (M old) w i : K₀) : ℝ)) (r : ℚ) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (v : Fin q → F),
      (∀ i, (v i : ℝ) = ((squareNorm (M old) w i : K₀) : ℝ) ^ (r : ℝ)) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun l i j => IntermediateField.inclusion h₀ (M l i j))
          (appendOne (fun l i => IntermediateField.inclusion h₀
            (appendOne U (squareNorm (M old) w) l i)) v)
          (fun i => IntermediateField.inclusion h₀ (w i)))
        (evaluationProblem basis M U w)) := by
  have initial : PromisePolyTimeTuringReduction
      (evaluationProblem basis M (appendOne U (squareNorm (M old) w)) w)
      (evaluationProblem basis M U w) := by
    simpa only [pow_one] using squareNormPowerUnaryReduction basis M U w old hs 1
  obtain ⟨F,h₀,e,bF,v,hv,hr⟩ := exists_joint_power_available basis M
    (appendOne U (squareNorm (M old) w)) w (Fin.last ut)
    (by simpa only [appendOne_aux] using hpos) r (evaluationProblem basis M U w) initial
  exact ⟨F,h₀,e,bF,v,by simpa only [appendOne_aux] using hv,hr⟩

/-- In particular the actual inverse positive square root is available, with
its field and program constructed from the source instead of postulated. -/
theorem exists_squareNorm_inverse_sqrt_unary
    (basis : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (w : Fin q → K₀) (old : Fin bt) (hs : ∀ i j, M old i j = M old j i)
    (hpos : ∀ i, 0 < ((squareNorm (M old) w i : K₀) : ℝ)) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (v : Fin q → F),
      (∀ i, (v i : ℝ) = (Real.sqrt ((squareNorm (M old) w i : K₀) : ℝ))⁻¹) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun l i j => IntermediateField.inclusion h₀ (M l i j))
          (appendOne (fun l i => IntermediateField.inclusion h₀
            (appendOne U (squareNorm (M old) w) l i)) v)
          (fun i => IntermediateField.inclusion h₀ (w i)))
        (evaluationProblem basis M U w)) := by
  obtain ⟨F,h₀,e,bF,v,hv,hr⟩ := exists_squareNorm_rational_unary basis M U w old hs hpos (-1/2)
  refine ⟨F,h₀,e,bF,v,?_,hr⟩
  intro i
  rw [hv i]
  have he : ((-1 / 2 : ℚ) : ℝ) = -(1 / (2 : ℝ)) := by norm_num
  rw [he,Real.rpow_neg (hpos i).le,← Real.sqrt_eq_rpow]

end PlanarHom.FixedSquareNormSource

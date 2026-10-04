import PlanarHom.WeightedBlockTractabilityConditional
import PlanarHom.PositiveIsingFoundationClosed

/- NEW adaptation of the recovered algebraic converse to the now-proved
ordinary Ising foundation; the displayed form and original source are unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual real-algebraic converse of Lemma 12.4

The source is the original canonical real-algebraic language and the result
uses its own field codec and ordinary graph problem. Tensor parameters are
not assumed to belong to that source field. This is not a claim about the
unfinished arbitrary-real Appendix A computational model.
-/
noncomputable section
open Classical
namespace PlanarHom.CenteredLogStructural
open Boolean Structures AlgebraicProductInterpolation

/-- A scaled tensor with constant positive weight is one permitted positive
block. The amplitude is the positive square root of the scale. -/
theorem scaled_tensor_allowedBlock {C : Type} {d : ℕ}
    (M : Matrix C C ℝ) (w : C → ℝ) (e : C ≃ Cube d)
    (γ μ : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (ρ : Fin d → ℝ) (hρ : ∀ r, 0 < ρ r ∧ ρ r ≠ 1)
    (hM : ∀ i j, M i j = γ * tensor ρ (e i) (e j))
    (hw : ∀ i, w i = μ) : AllowedWeightedBlock M w := by
  let ec : C ≃ Fin 1 × Cube d := {
    toFun := fun i => (0, e i)
    invFun := fun p => e.symm p.2
    left_inv := fun i => e.symm_apply_apply i
    right_inv := fun p => Prod.ext (Subsingleton.elim _ _) (e.apply_symm_apply p.2) }
  refine .positive 1 d (by omega) (fun _ => Real.sqrt γ) (fun _ => μ) ρ
    (fun _ => Real.sqrt_pos.2 hγ) (fun _ => hμ) hρ ec ?_ hw
  intro i j
  simpa only [ec, Real.mul_self_sqrt hγ.le] using hM i j

/-- Every displayed form in Lemma 12.4 has an actual polynomial-time
algorithm on the original canonical real-algebraic source encoding. -/
theorem tensor_form_inFP {q d : ℕ} (L : RealLanguage q 1 0)
    (e : Fin q ≃ Cube d) (γ μ : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (ρ : Fin d → ℝ) (hρ : ∀ r, 0 < ρ r ∧ ρ r ≠ 1)
    (hM : ∀ i j, L.matrices 0 i j = γ * tensor ρ (e i) (e j))
    (hw : ∀ i, L.weights i = μ) : L.problem.InFP := by
  have hf:=WeightedBlockTractability.allowedWeightedBlock_inFP_of_ising
    BooleanTensorEasyAssembly.positiveIsingFoundation L.field L.basis (L.matricesK 0) L.weightsK
    (scaled_tensor_allowedBlock (L.matrices 0) L.weights e γ μ hγ hμ ρ hρ hM hw)
  have hm:L.matricesK=(fun _:Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  change (Complexity.MixedCode.evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hm,hu]
  exact hf

end PlanarHom.CenteredLogStructural

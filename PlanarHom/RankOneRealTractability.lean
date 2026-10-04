import PlanarHom.RankOneEvaluationMachine
import PlanarHom.AlgebraicProductInterpolation
import PlanarHom.FixedFieldEncodingTransport

/-! The rank-one tractable form in the original real-algebraic source codec.
Amplitude algebraicity follows from the source diagonals, and actual linear
output descent removes the fixed amplitude extension. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FixedFieldEncodingTransport
variable {q : ℕ} (L : RealLanguage q 1 0)

theorem rankOne_amplitudes_algebraic (a : Fin q→ℝ)
    (h : ∀i j,L.matrices 0 i j=a i*a j) : ∀i,IsAlgebraic ℚ (a i) := by
  intro i
  apply IsAlgebraic.of_pow (n:=2) (by norm_num)
  simpa only [pow_two,←h i i] using L.matrices_algebraic 0 i i

/-- Actual promised polynomial time on every raw planar input, with original
source field/basis and no planarity recognizer, arithmetic oracle or amplitude
encoding assumed. This is only the rank-one part of Proposition2.6. -/
theorem rankOne_inFP (a : Fin q→ℝ) (h : ∀i j,L.matrices 0 i j=a i*a j) : L.problem.InFP := by
  let F := extensionField L.field a
  let φ := sourceInclusion L.field a
  let basis := extensionBasis L.field a (L.rankOne_amplitudes_algebraic a h)
  let aF : Fin q→F := targetValue L.field a
  let wF : Fin q→F := fun i=>φ (L.weightsK i)
  obtain ⟨back,hback,hfp⟩ := exists_fp_leftInverse L.basis basis φ.toLinearMap φ.injective
  have hm : (fun l i j=>φ (L.matricesK l i j))=(fun _ : Fin 1=>fun i j=>aF i*aF j) := by
    funext l i j
    have hl : l=0 := Subsingleton.elim _ _
    subst l
    apply Subtype.ext
    exact h i j
  have hu : (fun l i=>φ (L.unariesK l i))=(fun l : Fin 0=>Fin.elim0 l) := by
    funext l
    exact Fin.elim0 l
  apply (evaluation_inFP_iff L.basis L.matricesK L.unariesK L.weightsK).mpr
  have hv : FP (encoding.restrict (PlanarValid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _=>rfl)
  have he := (hv.comp (RankOneEvaluationMachine.fp_evaluate basis aF wF)).comp hfp
  apply he.congr
  intro g
  have hvalue := map_evaluate φ.toRingHom g.val g.property.1 L.matricesK L.unariesK L.weightsK
  change φ (g.val.evaluate g.property.1 L.matricesK L.unariesK L.weightsK)=
    g.val.evaluate g.property.1 (fun l i j=>φ (L.matricesK l i j))
      (fun l i=>φ (L.unariesK l i)) wF at hvalue
  rw [hm,hu,GraphDegreeMachines.rankOne_evaluate] at hvalue
  change back (RankOneEvaluationMachine.evaluate aF wF g.val)=_
  rw [show RankOneEvaluationMachine.evaluate aF wF g.val=
    φ (g.val.evaluate g.property.1 L.matricesK L.unariesK L.weightsK) from hvalue.symm]
  exact hback _

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

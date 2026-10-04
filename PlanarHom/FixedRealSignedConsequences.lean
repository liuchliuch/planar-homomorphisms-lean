import PlanarHom.FixedRealNonnegativeDichotomy
import PlanarHom.RealAppendixTransformEndpoints
import PlanarHom.FixedRealSupportDichotomy

/-! NEW complete A.14: actual signed support/magnitude reductions, weighted
support hardness, the unit-weight magnitude obstruction, and the full positive
weight zero-one dichotomy, all in the original prescribed represented field. -/
noncomputable section
namespace PlanarHom.FixedRealSignedConsequences
open DensePolynomial FixedRealExtension RepresentedBit Structures
open FixedRealMixedInterpolation FixedRealSignedTransforms FixedRealSupportHardness
open RootedRestriction ZeroOneBasicStructure
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K) (φ : K →+* ℝ)

 theorem magnitude_hard (M : Matrix (Fin q) (Fin q) K) (hs : ∀i j, M i j = M j i)
    (hbad : ¬NonnegativeClass (fun i j => |φ (M i j)|)) :
    RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M)
      (fun l : Fin 0 => l.elim0) (fun _ => 1)) := by
  let A : Matrix (Fin q) (Fin q) K := fun i j => magnitude φ (M i j)
  have hsA : ∀i j, A i j = A j i := by intro i j; dsimp [A]; rw [hs i j]
  have hA : ¬NonnegativeClass (fun i j => φ (A i j)) := by
    simpa only [A,magnitude_image] using hbad
  have hh := FixedRealApproximation.theoremA6_hard basis φ A hsA
    (fun i j => by simpa only [A,magnitude_image] using abs_nonneg (φ (M i j))) hA
  exact hh.trans (magnitudeReduction φ basis M (fun l : Fin 0 => l.elim0) (fun _ => 1))

 theorem theoremA14 (M : Matrix (Fin q) (Fin q) K) (hs : ∀i j, M i j = M j i)
    (w : Fin q → K) (hw : ∀i, 0 < φ (w i)) :
    (Nonempty (Reduction (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => fun i j => support (M i j)) (fun l : Fin 0 => l.elim0) w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => magnitude φ (M i j))
        (fun l : Fin 0 => l.elim0) w))) ∧
    (Nonempty (Reduction (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => fun i j => magnitude φ (M i j)) (fun l : Fin 0 => l.elim0) w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w))) ∧
    ((∃c : (colorSupport (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j))).ConnectedComponent,
      ¬BasicZeroOneComponent (fun i j : c.supp => if φ (M i.val j.val) = 0 then 0 else 1)) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) ∧
    ((∀i, w i = 1) → ¬NonnegativeClass (fun i j => |φ (M i j)|) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) ∧
    ((∀i j, M i j = 0 ∨ M i j = 1) →
      (BasicSupport φ M hs → (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP) ∧
      (¬BasicSupport φ M hs → RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w))) := by
  have chain := theoremA7_chain basis φ M (fun l : Fin 0 => l.elim0) w
  refine ⟨chain.1,chain.2,theoremA9_hard basis φ M hs w hw,?_,theoremA9_zeroOne basis φ M hs w hw⟩
  intro hunit hbad
  have he : w = fun _ => 1 := funext hunit
  rw [he]
  exact magnitude_hard basis φ M hs hbad

end PlanarHom.FixedRealSignedConsequences

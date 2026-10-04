import PlanarHom.FixedRealThreeStateEasy
import PlanarHom.FixedRealThreeStateHardness

/-! NEW full fixed-real Theorem 2.3 in a prescribed honest represented field.
The structural predicate is the exact frozen signed three-state criterion;
the source field is not assumed finite-dimensional over Q. -/
noncomputable section
namespace PlanarHom.FixedRealSmallState
open DensePolynomial FixedRealGraphEvaluation SignedThreeState RepresentedBit
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theorem23 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin 3) (Fin 3) K) (hs : ∀i j, M i j = M j i) :
    (ThreeStateEasy (fun i j => φ (M i j)) →
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M)
        (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP) ∧
    (¬ThreeStateEasy (fun i j => φ (M i j)) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1))) :=
  ⟨fun h => inFP basis M (fun _ => 1) (three_easy basis φ M hs h), theorem23_hard basis φ M hs⟩

end PlanarHom.FixedRealSmallState

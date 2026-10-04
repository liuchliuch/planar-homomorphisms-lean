import PlanarHom.FixedRealNonnegativeTractability
import PlanarHom.RealNonnegativeHardness

/-! NEW complete represented A.6 assembly. Both independent runtime and
hardness witnesses are instantiated in the identical prescribed source field. -/
noncomputable section
namespace PlanarHom.FixedRealApproximation
open DensePolynomial RepresentedBit
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theoremA6 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K)
    (hs : ∀i j, M i j = M j i) (hnn : ∀i j, 0 ≤ φ (M i j)) :
    (Structures.NonnegativeClass (fun i j => φ (M i j)) →
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M)
        (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP) ∧
    (¬Structures.NonnegativeClass (fun i j => φ (M i j)) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1))) :=
  ⟨theoremA6_easy basis φ M,theoremA6_hard basis φ M hs hnn⟩

end PlanarHom.FixedRealApproximation

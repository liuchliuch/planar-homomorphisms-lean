import PlanarHom.RealNonnegativeRationalObstruction
import PlanarHom.RealRationalOracleDescent
import PlanarHom.RealApproximationRepresented
import PlanarHom.FixedRealFiniteReplacement
import PlanarHom.MainDichotomyFinalAssembly
import PlanarHom.PositivePottsFoundationClosed

/-! NEW A.6 hard direction in the honest represented fixed-real model. A fixed
rational obstruction is chosen outside the original closed structural family;
the proved algebraic classification and actual answer descent supply hardness.
No approximation or output conversion is supplied as an oracle premise. -/
noncomputable section
namespace PlanarHom.FixedRealApproximation
open DensePolynomial FixedRealExtension Complexity RepresentedBit ProductCompatibility
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theoremA6_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K)
    (hs : ∀i j, M i j = M j i) (hnn : ∀i j, 0 ≤ φ (M i j))
    (hbad : ¬Structures.NonnegativeClass (fun i j => φ (M i j))) :
    RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1)) := by
  obtain ⟨N,hNs,hNpos,hzero,hNbad,hcompat⟩ := rational_obstruction
    (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j)) hnn hbad
  let L := rationalLanguage N
  have hhard : PromisedSharpPHard L.problem :=
    (L.theorem11_of_potts AlgebraicProductInterpolation.RealLanguage.positivePottsFoundation
      (fun _ => rfl) (fun i j => by change (N i j : ℝ) = (N j i : ℝ); exact_mod_cast hNs i j)
      (fun i j => by change (0 : ℝ) ≤ (N i j : ℝ); exact_mod_cast hNpos i j)).2 hNbad
  have hr := (RepresentedBit.SharpPHard.ofCanonical hhard).trans (rationalOracleDescent basis N)
  have hm : HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2)
      (fun p => (N p.1 p.2 : K)) := by
    apply hasProductMaps_of_compatible
    apply Compatible.of_injective_map φ
    simpa only [map_ratCast] using hcompat
  have r := FixedRealMixedInterpolation.finiteReplacementReduction basis M
    (fun _ : Fin 1 => fun i j => (N i j : K)) (fun l : Fin 0 => l.elim0) (fun _ => 1)
    (fun _ i j h => by simp [(hzero i j).mpr (by simp [h])]) (fun _ => hm)
  exact hr.trans r

end PlanarHom.FixedRealApproximation

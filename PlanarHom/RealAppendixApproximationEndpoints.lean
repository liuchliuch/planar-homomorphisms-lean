import PlanarHom.RealApproximationRepresented
import PlanarHom.FixedRealFiniteReplacement

/-! NEW standalone A.4 endpoint: a single fixed rational symmetric target is
computed by an actual oracle reduction to the original real-parameter problem.
Only mathematical fixed constants are chosen; all variable graph work is FP. -/
noncomputable section
namespace PlanarHom.FixedRealApproximation
open DensePolynomial FixedRealExtension Complexity RepresentedBit FiniteLanguageAliases
variable {n e q u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theoremA4 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K)
    (hs : ∀i j, M i j = M j i) (δ : ℝ) (hδ : 0 < δ) :
    ∃N : Matrix (Fin q) (Fin q) ℚ,
      (∀i j, N i j = N j i) ∧ (∀i j, N i j = 0 ↔ M i j = 0) ∧
      (∀i j, |(N i j : ℝ) - φ (M i j)| < δ) ∧
      (∀i j, Real.sign (N i j : ℝ) = Real.sign (φ (M i j))) ∧
      Nonempty (Reduction (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => fun i j => (N i j : K)) U w)
        (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)) := by
  obtain ⟨N,hNs,hNz,hNa,hNsg,⟨r⟩⟩ := theoremA4_joint basis φ (fun _ : Fin 1 => M) U w
    (fun _ => hs) δ hδ (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)
    (FixedRealMixedInterpolation.identityReduction basis _ U w)
  refine ⟨N 0,hNs 0,hNz 0,hNa 0,hNsg 0,?_⟩
  have select := FixedRealMixedInterpolation.binaryRelabelReduction basis
    (fun _ : Fin 1 => Fin.natAdd 1 (0 : Fin 1))
    (appendFamily (fun _ : Fin 1 => M) (fun l i j => (N l i j : K))) U w
  have he : (appendFamily (fun _ : Fin 1 => M) (fun l i j => (N l i j : K))) ∘
      (fun _ : Fin 1 => Fin.natAdd 1 (0 : Fin 1)) = (fun _ : Fin 1 => fun i j => (N 0 i j : K)) :=
    funext (fun _ => appendFamily_new _ _ 0)
  rw [he] at select
  exact ⟨select.trans r⟩

end PlanarHom.FixedRealApproximation

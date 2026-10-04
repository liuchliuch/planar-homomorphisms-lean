import PlanarHom.FixedRealNonnegativeDichotomy
import PlanarHom.RankFourPositiveRefinement
import PlanarHom.RankFourBooleanOriginalCriterion

/-! NEW full fixed-real cited Theorem 2.4, preserving rank four, both nonempty
split sizes, and the literal signed Boolean equations on its nonnegative
factors. The original source field remains the output presentation. -/
noncomputable section
namespace PlanarHom.FixedRealSmallState
open DensePolynomial RepresentedBit Structures RankFour FixedRealApproximation
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theorem24 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin 4) (Fin 4) K)
    (hs : ∀i j, M i j = M j i) (hnn : ∀i j, 0 ≤ φ (M i j))
    (hr : Matrix.rank (fun i j => φ (M i j)) = 4) :
    (FourStateClass (fun i j => φ (M i j)) →
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M)
        (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP) ∧
    (¬FourStateClass (fun i j => φ (M i j)) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1))) := by
  have h := theoremA6 basis φ M hs hnn
  have he := nonnegativeClass_iff_fourStateClass hr
  exact ⟨fun hc => h.1 (he.mpr hc),fun hn => h.2 (fun hc => hn (he.mp hc))⟩

 theorem theorem24_positive (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin 4) (Fin 4) K)
    (hs : ∀i j, M i j = M j i) (hp : ∀i j, 0 < φ (M i j))
    (hr : Matrix.rank (fun i j => φ (M i j)) = 4) :
    (PositiveFourTensor (fun i j => φ (M i j)) →
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M)
        (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP) ∧
    (¬PositiveFourTensor (fun i j => φ (M i j)) →
      RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1))) := by
  have h := theoremA6 basis φ M hs (fun i j => (hp i j).le)
  have he := positive_nonnegativeClass_iff_tensor hp hr
  exact ⟨fun hc => h.1 (he.mpr hc),fun hn => h.2 (fun hc => hn (he.mp hc))⟩

/-- The smaller displayed direct-sum blocks have genuine algorithms in the
original prescribed field. Their entries are extracted from M, so field
membership and runtime are proved rather than supplied as a block oracle. -/
 theorem directSum_block_algorithms (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin 4) (Fin 4) K) {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ)
    (p : Fin 4 ≃ Fin a ⊕ Fin b)
    (hm : ∀i j, φ (M (p.symm i) (p.symm j)) = sumMatrix A B i j)
    (hA : NonnegativeClass A) (hB : NonnegativeClass B) :
    (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j : Fin a =>
        M (p.symm (.inl i)) (p.symm (.inl j))) (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP ∧
    (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j : Fin b =>
        M (p.symm (.inr i)) (p.symm (.inr j))) (fun l : Fin 0 => l.elim0) (fun _ => 1)).InFP := by
  constructor
  · apply theoremA6_easy basis φ
    have he : (fun i j : Fin a => φ (M (p.symm (.inl i)) (p.symm (.inl j)))) = A :=
      funext (fun i => funext (fun j => hm (.inl i) (.inl j)))
    rwa [he]
  · apply theoremA6_easy basis φ
    have he : (fun i j : Fin b => φ (M (p.symm (.inr i)) (p.symm (.inr j)))) = B :=
      funext (fun i => funext (fun j => hm (.inr i) (.inr j)))
    rwa [he]

end PlanarHom.FixedRealSmallState

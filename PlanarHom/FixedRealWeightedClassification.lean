import PlanarHom.FixedRealWeightedTractability
import PlanarHom.FixedRealWeightedNecessity

/-! A.12 final assembly from the genuine rectangular-moment, weighted support
and actual-row quotient proofs. No hardness or availability premise remains. -/
noncomputable section
namespace PlanarHom.FixedRealWeightedClassification
open DensePolynomial RepresentedBit FixedRealMixedInterpolation Structures
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

theorem theoremA12 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K) (hs : ∀ i j,M i j=M j i)
    (hnn : ∀ i j,0≤φ (M i j)) (w : Fin q → K) (hw : ∀ i,0<φ (w i)) :
    (PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) →
        (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP) ∧
    (¬PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) →
        SharpPHard (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) := by
  refine ⟨FixedRealGraphEvaluation.positiveVertexWeightClass_inFP basis φ M w hs,?_⟩
  intro hbad
  by_contra hn
  exact hbad (FixedRealWeightedNecessity.positiveVertexWeightClass_of_not_hard basis φ M hs hnn w hw hn)

end PlanarHom.FixedRealWeightedClassification

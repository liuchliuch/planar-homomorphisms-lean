import PlanarHom.AlgebraicProductInterpolation
import PlanarHom.PromisedSharpPHardness
import PlanarHom.Structures
import PlanarHom.DomainDoublingLiteralCorollary

/-! Independently written review contracts. These definitions state propositions;
they contain no proof placeholders and do not import Audit.Solutions. Their
transitive model dependencies are part of the trusted review surface. -/
noncomputable section
open PlanarHom.AlgebraicProductInterpolation PlanarHom.Complexity PlanarHom.Structures
open PlanarHom.DomainDoublingClassification

namespace PlanarHomAudit.Contracts

def theorem11 : Prop :=
  ∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)

def theorem13 : Prop :=
  ∀ {q : ℕ} (L : RealLanguage q 1 0)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i),
    (∀ i j, 0 ≤ L.matrices 0 i j) → (∀ i, 0 < L.weights i) →
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem)

def corollary122_rectangular : Prop :=
  ∀ {x y : ℕ} (V : Matrix (Fin x) (Fin y) ℝ)
    (μ : Fin x → ℝ) (ν : Fin y → ℝ)
    (hV : ∀ i j, IsAlgebraic ℚ (V i j))
    (hμ : ∀ i, IsAlgebraic ℚ (μ i)) (hν : ∀ i, IsAlgebraic ℚ (ν i)),
    (∀ i j, 0 ≤ V i j) → (∀ i, 0 < μ i) → (∀ i, 0 < ν i) →
    let L := rectangularLanguage V μ ν hV hμ hν
    (PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      (prescribedProblem L rectangularSide).InFP) ∧
    (¬PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      PromisedSharpPHard (prescribedProblem L rectangularSide))

end PlanarHomAudit.Contracts

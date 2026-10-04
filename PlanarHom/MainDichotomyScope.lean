import PlanarHom.PromisedSharpPHardness
import PlanarHom.MainSourceQuotientFacts
import PlanarHom.MainStructuralSupportTransport

/-! Exact source statements of Theorems 1.1 and 1.3. These are definitions of
proof goals, not claims that the main theorems have been proved. -/
noncomputable section
namespace PlanarHom.MainDichotomyScope
open AlgebraicProductInterpolation Complexity Structures

def Theorem11Statement : Prop :=
  ∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)

def Theorem13Statement : Prop :=
  ∀ {q : ℕ} (L : RealLanguage q 1 0)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i),
    (∀ i j, 0 ≤ L.matrices 0 i j) → (∀ i, 0 < L.weights i) →
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem)

/-- The predicate in 1.3 uses the complete identical-row quotient and the
original class-weight sums; it is not a row-injectivity assumption on L. -/
theorem theorem13_structure_iff {q : ℕ} (L : RealLanguage q 1 0)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i) :
    PositiveVertexWeightClass (L.matrices 0) L.weights hs ↔
      WeightedClass ((L.fullQuotientLanguage hs).matrices 0)
        (L.fullQuotientLanguage hs).weights :=
  (L.fullQuotient_weighted_class_iff hs).symm

end PlanarHom.MainDichotomyScope

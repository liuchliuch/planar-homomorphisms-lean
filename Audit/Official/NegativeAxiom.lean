import Audit.Solutions

noncomputable section
open scoped BigOperators Classical
open PlanarHom.AlgebraicProductInterpolation PlanarHom.Complexity PlanarHom.Structures
open PlanarHom.DomainDoublingClassification
namespace PlanarHomAudit.Comparator

axiom unexpected :
  (∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem))

theorem theorem11 :
  (∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)) := unexpected

end PlanarHomAudit.Comparator

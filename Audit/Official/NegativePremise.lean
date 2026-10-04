import Audit.Solutions

noncomputable section
open scoped BigOperators Classical
open PlanarHom.AlgebraicProductInterpolation PlanarHom.Complexity PlanarHom.Structures
open PlanarHom.DomainDoublingClassification
universe u_1 u_2
namespace PlanarHomAudit.Comparator

theorem theorem11 : False →
  (∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)) :=
  fun _ => @PlanarHomAudit.Solutions.theorem11

end PlanarHomAudit.Comparator

import PlanarHom.SandwichMaximality
import PlanarHom.WeightedSquareRigidity
import PlanarHom.SandwichLinearRigidity

/-!
# Original opposite-square entries from rational candidate bounds

The proof derives support containment, identifies the actual logarithmic graph
of rational sandwiches, applies proved weighted-shortest-path rigidity, and
extracts the original entries on two rational slopes. No opposite-edge or
path-product identity is assumed. Computational availability remains separate
from the explicit numerical candidate bounds.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
namespace PlanarHom.SandwichMaximality
open LogarithmicSupport MatrixLogCoefficients SymmetricBCH MaximumLogarithmicSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit numerical bounds for Schur curves of actual admissible rational
sandwiches. The right-hand side is the fixed source edge count; no logarithmic
support equality, path identity, or desired coefficient appears as a premise. -/
def RationalSandwichSchurEdgeBound (C B : Matrix V V ℝ) (hC : C.IsHermitian) : Prop :=
  ∀ η q : ℚ, 0 < η → 0 < q →
    (sandwich C ((η : ℝ) • B) q).PosDef →
    (∀ i j, 0 < sandwich C ((η : ℝ) • B) q i j) →
    ∀ s : ℕ, 0 < s → Even s → ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℚ, 0 < u → (u : ℝ) < ε →
        (schurExp (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) s u).PosDef →
        (offDiagonalSupport
          (schurExp (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) s u)
          (schurExp_isHermitian (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) IsSelfAdjoint.log s u)).Connected →
        (∀ i j, 0 ≤ schurExp (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) s u i j) →
        (logSupport (schurExp (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) s u)).edgeFinset.card ≤
          (offDiagonalSupport C hC).edgeFinset.card

/-- Actual rational log-sandwich entries agree on opposite edges of each
geodesic square, derived entirely from the three numerical candidate bounds. -/
theorem rational_sandwich_opposite_square_log_entries_eq
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hG : (offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC)
    (hschur : RationalSandwichSchurEdgeBound C B hC)
    (v₁ v₂ v₃ v₄ : V)
    (h₁₂ : (offDiagonalSupport C hC).Adj v₁ v₂)
    (h₂₃ : (offDiagonalSupport C hC).Adj v₂ v₃)
    (h₃₄ : (offDiagonalSupport C hC).Adj v₃ v₄)
    (h₄₁ : (offDiagonalSupport C hC).Adj v₄ v₁)
    (hd₁₃ : (offDiagonalSupport C hC).dist v₁ v₃ = 2)
    (hd₂₄ : (offDiagonalSupport C hC).dist v₂ v₄ = 2) :
    ∃ δ > 0, ∀ η : ℚ, 0 < η → (η : ℝ) < δ →
      ∃ ε > 0, ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
        EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q) v₁ v₂ =
          EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q) v₃ v₄ ∧
        EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q) v₂ v₃ =
          EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q) v₄ v₁ := by
  have hs := supportedOn_of_rational_squareSandwich_maximality C B hC hB hG hedge hsquare
  obtain ⟨δ, hδ, hr⟩ := rational_sandwich_logSupport_eq_of_maximal C B hC hB hG hedge hs hraw
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  obtain ⟨ε, hε, hentry⟩ := hr η hη hηδ
  refine ⟨ε, hε, ?_⟩
  intro q hq hqε
  obtain ⟨hpd, hpos, heq, hlogpos⟩ := hentry q hq hqε
  have hSchurBound : RationalSchurEdgeBound
      (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) IsSelfAdjoint.log := by
    intro s hs heven
    obtain ⟨ζ, hζ, hm⟩ := hschur η q hη hq hpd hpos s hs heven
    refine ⟨ζ, hζ, ?_⟩
    intro u hu huζ hupd huconn hunonneg
    have h := hm u hu huζ hupd huconn hunonneg
    change (logSupport (schurExp (EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q)) s u)).edgeFinset.card ≤
      (logSupport (sandwich C ((η : ℝ) • B) q)).edgeFinset.card
    rw [heq]
    exact h
  exact opposite_log_square_entries_eq (sandwich C ((η : ℝ) • B) q)
    (offDiagonalSupport C hC) heq hG hlogpos hSchurBound
    v₁ v₂ v₃ v₄ h₁₂ h₂₃ h₃₄ h₄₁ hd₁₃ hd₂₄

/-- The original matrices themselves have equal opposite-square entries,
extracted from actual rational-time logarithmic equalities on two slopes. -/
theorem opposite_square_entries_of_sandwich_maximality
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hG : (offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC)
    (hschur : RationalSandwichSchurEdgeBound C B hC)
    (v₁ v₂ v₃ v₄ : V)
    (h₁₂ : (offDiagonalSupport C hC).Adj v₁ v₂)
    (h₂₃ : (offDiagonalSupport C hC).Adj v₂ v₃)
    (h₃₄ : (offDiagonalSupport C hC).Adj v₃ v₄)
    (h₄₁ : (offDiagonalSupport C hC).Adj v₄ v₁)
    (hd₁₃ : (offDiagonalSupport C hC).dist v₁ v₃ = 2)
    (hd₂₄ : (offDiagonalSupport C hC).dist v₂ v₄ = 2) :
    C v₁ v₂ = C v₃ v₄ ∧ C v₂ v₃ = C v₄ v₁ ∧
      B v₁ v₂ = B v₃ v₄ ∧ B v₂ v₃ = B v₄ v₁ := by
  letI : Nonempty V := hG.nonempty
  obtain ⟨δ, hδ, hrelations⟩ := rational_sandwich_opposite_square_log_entries_eq
    C B hC hB hG hedge hsquare hraw hschur v₁ v₂ v₃ v₄ h₁₂ h₂₃ h₃₄ h₄₁ hd₁₃ hd₂₄
  have hfirst := entries_eq_of_rational_sandwich_log_sector C B hC hB δ hδ v₁ v₂ v₃ v₄
    (fun η hη hηδ => by
      obtain ⟨ε, hε, hr⟩ := hrelations η (by exact_mod_cast hη) hηδ
      exact ⟨ε, hε, fun q hq hqε => (hr q (by exact_mod_cast hq) hqε).1⟩)
  have hsecond := entries_eq_of_rational_sandwich_log_sector C B hC hB δ hδ v₂ v₃ v₄ v₁
    (fun η hη hηδ => by
      obtain ⟨ε, hε, hr⟩ := hrelations η (by exact_mod_cast hη) hηδ
      exact ⟨ε, hε, fun q hq hqε => (hr q (by exact_mod_cast hq) hqε).2⟩)
  exact ⟨hfirst.1, hsecond.1, hfirst.2, hsecond.2⟩

end PlanarHom.SandwichMaximality

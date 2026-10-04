import PlanarHom.OccurrencePfaffianPairings
import PlanarHom.FisherMatchingBoundary

/-!
# Exact Fisher reference-sign calibration

These are conditional algebraic consequences of a supplied, verified
`IsPfaffianOrientation`. They do not construct that orientation, compute an
embedding/order, evaluate a Pfaffian in polynomial time, or assert `InFP`.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The explicit external-edge matching supplies the global sign without any
search for a nonvanishing weighted matching. -/
theorem cubicMatching_eq_referenceSign_pfaffian [LinearOrder (V × Fin 3)]
    (p : (V × Fin 3) ≃ (E × Bool)) (orientation : E ⊕ (V × Fin 3) → Bool)
    (ho : (cubicDecoration p).IsPfaffianOrientation orientation) (w : E ⊕ (V × Fin 3) → ℝ) :
    (cubicDecoration p).perfectMatchingSum w =
      (cubicDecoration p).matchingPfaffianSign orientation referenceMatching *
        pairingPfaffian ((cubicDecoration p).occurrenceSkewMatrix orientation w) :=
  perfectMatchingSum_eq_referenceSign_mul_pairingPfaffian (cubicDecoration p)
    orientation ho referenceMatching (referenceMatching_perfect p) w

/-- On the Fisher polynomial weights, the reference term is exactly its sign,
even when some other weights vanish or are negative. -/
theorem cubic_reference_signedTerm [LinearOrder (V × Fin 3)]
    (p : (V × Fin 3) ≃ (E × Bool)) (orientation : E ⊕ (V × Fin 3) → Bool) (x : E → ℝ) :
    (cubicDecoration p).matchingPfaffianSign orientation referenceMatching *
      (∏ e ∈ referenceMatching, cubicPolynomialWeight p x e) =
        (cubicDecoration p).matchingPfaffianSign (R := ℝ) orientation referenceMatching := by
  rw [referenceMatching_weight, mul_one]

variable {G : MultiGraph V E}

/-- The arbitrary-input Fisher output has an exact, sign-correct Pfaffian
identity under precisely the remaining orientation certificate. -/
theorem fisherMatching_eq_referenceSign_pfaffian (o : G.IncidenceOrdering)
    [LinearOrder (ExpansionVertex o × Fin 3)]
    (orientation : ExpansionEdge o ⊕ (ExpansionVertex o × Fin 3) → Bool)
    (ho : (fisherGraph o).IsPfaffianOrientation orientation) (x : E → ℝ) :
    (fisherGraph o).perfectMatchingSum (fisherWeight o x) =
      (fisherGraph o).matchingPfaffianSign orientation referenceMatching *
        pairingPfaffian ((fisherGraph o).occurrenceSkewMatrix orientation (fisherWeight o x)) :=
  cubicMatching_eq_referenceSign_pfaffian (expansionCubicPorts o) orientation ho _

/-- Conditional FKT algebra for the original zero-field Ising value. The order
and orientation are supplied explicitly; no algorithmic or planarity promise
has been silently converted to either piece of data. -/
theorem ising_eq_referenceSign_pfaffian (o : G.IncidenceOrdering)
    [LinearOrder (ExpansionVertex o × Fin 3)]
    (orientation : ExpansionEdge o ⊕ (ExpansionVertex o × Fin 3) → Bool)
    (ho : (fisherGraph o).IsPfaffianOrientation orientation)
    (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    G.partition (Boolean.W ρ) (fun _ => 1) =
      (((1 + ρ) / 2) ^ Fintype.card E / (2 : ℝ) ^ Fintype.card V) *
        ((fisherGraph o).matchingPfaffianSign orientation referenceMatching *
          pairingPfaffian ((fisherGraph o).occurrenceSkewMatrix orientation
            (fisherWeight o (fun _ => (1 - ρ) / (1 + ρ))))) := by
  rw [arbitrary_ising_matching o ρ hρ]
  exact congrArg (fun z : ℝ => (((1 + ρ) / 2) ^ Fintype.card E /
    (2 : ℝ) ^ Fintype.card V) * z)
      (fisherMatching_eq_referenceSign_pfaffian o orientation ho _)

end PlanarHom.Fisher

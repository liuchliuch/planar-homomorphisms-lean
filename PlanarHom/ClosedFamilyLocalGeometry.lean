import PlanarHom.AlgebraicClosedMatrixFamily
import PlanarHom.WheatstonePlanarGadget

/-! Source4.4: the Wheatstone candidate belongs to the same source-closed family
by an actual planar outer-face gadget, so its edge bound follows from maximum
cardinality. No common-neighbor or candidate-bound premise is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MaximumLogarithmicSupport WheatstoneCoefficients
variable {q : ℕ}

/-- Homogeneous planar edge-gadget closure, a subcase of the stated §4 closure. -/
structure PlanarGadgetClosed (A : Set (Matrix (Fin q) (Fin q) ℝ)) : Prop where
  signature_mem : ∀ (I E : Type) [Fintype I] [Fintype E] (G : TwoTerminal I E),
    TwoTerminal.PlanarEdgeGadget G → ∀ H ∈ A,
    (TwoTerminal.signature G H (fun _ => 1)).IsHermitian →
    TwoTerminal.signature G H (fun _ => 1) ∈ A

/-- The exact five-edge signature is in A by actual outer-cofacial planarity. -/
theorem wheatstone_mem (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hgadget : PlanarGadgetClosed A) (G : SimpleGraph (Fin q)) (x : ℚ)
    (hE : EntropyCompletion.distanceKernel G x ∈ A) : wheatstoneMatrix G x ∈ A := by
  rw [← TwoTerminal.signature_wheatstone_distanceKernel]
  apply hgadget.signature_mem Bool (Fin 5) TwoTerminal.wheatstone TwoTerminal.wheatstone_planarEdgeGadget _ hE
  rw [TwoTerminal.signature_wheatstone_distanceKernel]
  exact wheatstoneMatrix_isHermitian _ _

/-- Derive the Wheatstone cardinality bound from the same actual maximization
class, including candidate connectedness from strict positive entries. -/
theorem rationalWheatstoneEdgeBound (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : AlgebraicSourceClosed A) (htransfer : EffectiveSpectralClosed A)
    (hgadget : PlanarGadgetClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    RationalWheatstoneEdgeBound (logSupport M) := by
  have hc := logSupport_connected hM.posDef hM.connected
  letI : Nonempty (Fin q) := hc.nonempty
  refine ⟨1, by norm_num, ?_⟩
  intro x _ _ hpd hp
  have hm := wheatstone_mem A hgadget (logSupport M) x
    (distanceKernel_mem A htransfer M hM.mem hM.posDef (hA.algebraic M hM.mem) hc hpositive x)
  apply hmax _ ⟨hm, fun i j => (hp i j).le, hpd, ?_⟩
  constructor
  intro i j
  by_cases hij : i = j
  · subst j
    exact SimpleGraph.Reachable.refl _
  · exact (show (offDiagonalSupport _ hpd.1).Adj i j from ⟨hij, ne_of_gt (hp i j)⟩).reachable

/-- **Lemma4.4.** Exactly two nonadjacent common neighbors at distance two, and
clique components in every neighborhood, under the original source family rules. -/
theorem lemma44 (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : AlgebraicSourceClosed A) (htransfer : EffectiveSpectralClosed A)
    (hgadget : PlanarGadgetClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    CartesianGeometry.TwoCommonNeighbors (logSupport M) ∧
      CartesianGeometry.NeighborhoodCliques (logSupport M) := by
  have hc := logSupport_connected hM.posDef hM.connected
  have hs := rationalSchurEdgeBound A hA.toSpectralParallelClosed M hM hmax
  have hw := rationalWheatstoneEdgeBound A hA htransfer hgadget M hM hmax hpositive
  have ht := twoCommonNeighbors_of_rational_maximality (EntropyCompletion.matrixLog M)
    (cfc_predicate Real.log M) hc hpositive hs hw
  exact ⟨ht, ht.neighborhoodCliques⟩

end PlanarHom.ClosedMatrixFamily

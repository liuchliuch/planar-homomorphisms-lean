import PlanarHom.ClosedFamilyLocalGeometry

/-! Source4.7 assembled from the now proved source-closed family bounds and the
full positive-definite continuation/Cartesian graph characterization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator Topology
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixLogCoefficients MaximumLogarithmicSupport
variable {q : ℕ}

/-- Any maximizing graph has a positive-log representative with that same graph. -/
theorem exists_positive_same_graph (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : AlgebraicSourceClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M) :
    ∃ N, Admissible A N ∧ IsMaximum A N ∧ logSupport N = logSupport M ∧
      ∀ i j, (logSupport N).Adj i j → 0 < EntropyCompletion.matrixLog N i j := by
  have hc := logSupport_connected hM.posDef hM.connected
  have hbound := rationalSchurEdgeBound A hA.toSpectralParallelClosed M hM hmax
  have hL : (EntropyCompletion.matrixLog M).IsHermitian := cfc_predicate Real.log M
  obtain ⟨δ,hδ,hsupport⟩ := rational_schur_logSupport_eq_of_maximal
    (EntropyCompletion.matrixLog M) hL hc 2 (by decide) (by decide) (hbound 2 (by decide) (by decide))
  obtain ⟨r,hr,hrδ,hpd,hconn,hnn,_⟩ := WheatstoneCoefficients.exists_positive_rat_of_eventually
    (eventually_schurExp_admissible (EntropyCompletion.matrixLog M) hL hc 2 (by decide) (by decide)) hδ
  obtain ⟨_,heq,hpos⟩ := hsupport r hr hrδ
  let N := schurExp (EntropyCompletion.matrixLog M) 2 r
  refine ⟨N,⟨schurExp_log_mem A hA.toSpectralParallelClosed M hM 2 (by decide) r,hnn,hpd,hconn⟩,?_,heq,hpos⟩
  intro H hH
  rw [show logSupport N = logSupport M from heq]
  exact hmax H hH

/-- **Theorem4.7.** Every maximum logarithmic graph is an actual Cartesian
product of complete graphs. Factor sizes may differ; a singleton is the empty product. -/
theorem lemma47 (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : AlgebraicSourceClosed A) (htransfer : EffectiveSpectralClosed A)
    (hgadget : PlanarGadgetClosed A) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : Admissible A M) (hmax : IsMaximum A M) :
    ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
      Nonempty ((logSupport M) ≃g CartesianGeometry.hammingGraph (fun i => Fin (s i))) := by
  obtain ⟨N,hN,hNmax,heq,hpos⟩ := exists_positive_same_graph A hA M hM hmax
  have hc := logSupport_connected hN.posDef hN.connected
  have hs := rationalSchurEdgeBound A hA.toSpectralParallelClosed N hN hNmax
  have hw := rationalWheatstoneEdgeBound A hA htransfer hgadget N hN hNmax hpos
  have hk := rationalDistanceKernelEdgeBound A htransfer N hN hNmax (hA.algebraic N hN.mem) hpos
  have h := cartesian_product_of_three_rational_bounds (EntropyCompletion.matrixLog N)
    (cfc_predicate Real.log N) hc hpos hs hw hk
  change ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
    Nonempty ((logSupport N) ≃g CartesianGeometry.hammingGraph (fun i => Fin (s i))) at h
  simpa only [heq] using h

end PlanarHom.ClosedMatrixFamily

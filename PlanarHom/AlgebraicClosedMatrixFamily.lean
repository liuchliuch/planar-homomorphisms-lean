import PlanarHom.ClosedFamilyShortestPaths
import PlanarHom.ClosedFamilyDistanceKernels

/-! Source-facing §4 closure interfaces. Every member is explicitly symmetric
and real-algebraic. Each operation is assumed only with its source hypotheses;
the stronger real-family helper interfaces are derived, not imposed anew. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport
variable {V : Type} [Fintype V] [DecidableEq V]

structure AlgebraicSourceClosed (A : Set (Matrix V V ℝ)) : Prop where
  symmetric : ∀ H ∈ A, H.IsHermitian
  algebraic : ∀ H ∈ A, ∀ i j, IsAlgebraic ℚ (H i j)
  spectral : ∀ H ∈ A, H.PosDef → (∀ i j, IsAlgebraic ℚ (H i j)) → ∀ r : ℚ,
    cfc (fun x : ℝ => x ^ (r : ℝ)) H ∈ A
  parallel : ∀ H ∈ A, H.IsHermitian → ∀ K ∈ A, K.IsHermitian →
    (fun i j => H i j * K i j) ∈ A

def AlgebraicSourceClosed.toSpectralParallelClosed {A : Set (Matrix V V ℝ)}
    (hA : AlgebraicSourceClosed A) : SpectralParallelClosed A where
  rationalPower_mem := fun H hH hpd r => hA.spectral H hH hpd (hA.algebraic H hH) r
  entrywiseProduct_mem := fun H hH K hK => hA.parallel H hH (hA.symmetric H hH)
    K hK (hA.symmetric K hK)

/-- Source4.1 with its algebraicity convention explicit. The maximum is attained
before any input instance; candidates and their maximum bounds are derived. -/
theorem lemma41 (A : Set (Matrix V V ℝ)) (hA : AlgebraicSourceClosed A)
    (hne : ∃ H, Admissible A H) :
    ∃ M, Admissible A M ∧ IsMaximum A M ∧ (logSupport M).Connected ∧
      ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j :=
  exists_maximum_positive_log A hA.toSpectralParallelClosed hne

/-- Source4.3 permits N to have signed entries; only PD, the maximizing log graph
and positive log edges are required in addition to actual family membership. -/
theorem lemma43 (A : Set (Matrix V V ℝ)) (hA : AlgebraicSourceClosed A)
    (M N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hpd : N.PosDef) (hgraph : logSupport N = logSupport M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog N i j)
    (i j : V) : PathRigidity (logSupport M) (EntropyCompletion.matrixLog N) i j :=
  weighted_shortest_paths A hA.toSpectralParallelClosed M N hM hmax hN hpd hgraph hpositive i j

variable {q : ℕ}

/-- The structural portion of4.2 in the source algebraic closed family; the
independent actual uniform simulation is DistanceKernelAvailability.uniformReduction. -/
theorem lemma42_structural (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : AlgebraicSourceClosed A) (htransfer : EffectiveSpectralClosed A)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j) :
    (∀ x : ℚ, 0 < x → EntropyCompletion.distanceKernel (logSupport M) x ∈ A) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
        (EntropyCompletion.distanceKernel (logSupport M) x).PosDef ∧
        EntropyCompletion.logVanishesOnNonedges (logSupport M)
          (EntropyCompletion.distanceKernel (logSupport M) x) := by
  refine ⟨fun x _ => distanceKernel_mem A htransfer M hM.mem hM.posDef (hA.algebraic M hM.mem)
    (logSupport_connected hM.posDef hM.connected) hpositive x, ?_⟩
  exact distanceKernel_near_zero A htransfer M hM hmax (hA.algebraic M hM.mem) hpositive

end PlanarHom.ClosedMatrixFamily

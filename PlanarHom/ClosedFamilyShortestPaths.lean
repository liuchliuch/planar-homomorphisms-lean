import PlanarHom.ClosedFamilyPositiveLog

/-! Source4.3 from the actual matrix-family closure and global maximum. The
current matrix N need only be PD and have the maximizing logarithmic graph;
entrywise nonnegativity or connected numerical support is not added to N. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator Topology
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixLogCoefficients MaximumLogarithmicSupport
variable {V : Type} [Fintype V] [DecidableEq V]

theorem schurExp_log_mem_of_posDef (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (N : Matrix V V ℝ) (hN : N ∈ A) (hpd : N.PosDef) (s : ℕ) (hs : 0 < s) (r : ℚ) :
    schurExp (EntropyCompletion.matrixLog N) s r ∈ A := by
  have hp := hA.rationalPower_mem N hN hpd r
  have hh : (fun i j => (cfc (fun x : ℝ => x ^ (r : ℝ)) N) i j ^ s) ∈ A := by
    induction s with
    | zero => omega
    | succ s ih =>
      by_cases hz : s = 0
      · subst s
        simpa only [zero_add, pow_one] using hp
      · have hc := hA.entrywiseProduct_mem _ (ih (by omega)) _ hp
        simpa only [pow_succ] using hc
  convert hh using 1
  ext i j
  change NormedSpace.exp ℝ ((r : ℝ) • EntropyCompletion.matrixLog N) i j ^ s = _
  rw [← SpectralProductZeros.realPower_eq_exp_smul_log N hpd (r : ℝ)]
  rfl

/-- Equality with the maximizing graph gives the exact candidate edge bound. -/
theorem rationalSchurEdgeBound_of_same_graph (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (M N : Matrix V V ℝ) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hpd : N.PosDef) (hgraph : logSupport N = logSupport M) :
    RationalSchurEdgeBound (EntropyCompletion.matrixLog N) (cfc_predicate Real.log N) := by
  intro s hs _
  refine ⟨1, by norm_num, ?_⟩
  intro r _ _ hpd' hconn hnonneg
  have h := hmax _ ⟨schurExp_log_mem_of_posDef A hA N hN hpd s hs r, hnonneg, hpd', hconn⟩
  change _ ≤ (logSupport N).edgeFinset.card
  rw [hgraph]
  exact h

/-- Package the two genuine path conclusions so equality transport also carries
the implicit graph arguments of every walk. -/
def PathRigidity (G : SimpleGraph V) (L : Matrix V V ℝ) (i j : V) : Prop :=
  Fintype.card (ShortestPathWeights.ShortestPath G i j) = (G.dist i j).factorial ∧
    ∀ p q : ShortestPathWeights.ShortestPath G i j,
      ShortestPathWeights.walkWeight L p.val = ShortestPathWeights.walkWeight L q.val

/-- **Lemma4.3.** Genuine shortest paths are counted and their actual log-edge
products agree, with only the original family, maximum and N hypotheses. -/
theorem weighted_shortest_paths (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (M N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hpd : N.PosDef) (hgraph : logSupport N = logSupport M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog N i j)
    (i j : V) :
    Fintype.card (ShortestPathWeights.ShortestPath (logSupport M) i j) =
        ((logSupport M).dist i j).factorial ∧
      ∀ p q : ShortestPathWeights.ShortestPath (logSupport M) i j,
        ShortestPathWeights.walkWeight (EntropyCompletion.matrixLog N) p.val =
          ShortestPathWeights.walkWeight (EntropyCompletion.matrixLog N) q.val := by
  have hconn : (logSupport N).Connected := hgraph ▸ logSupport_connected hM.posDef hM.connected
  have hp : ∀ a b, (logSupport N).Adj a b → 0 < EntropyCompletion.matrixLog N a b := by
    intro a b hab
    exact hpositive a b (hgraph ▸ hab)
  have h := shortest_paths_rigid_of_rational_maximality
    (EntropyCompletion.matrixLog N) (cfc_predicate Real.log N) hconn hp
    (rationalSchurEdgeBound_of_same_graph A hA M N hmax hN hpd hgraph) i j
  change PathRigidity (logSupport N) (EntropyCompletion.matrixLog N) i j at h
  change PathRigidity (logSupport M) (EntropyCompletion.matrixLog N) i j
  exact hgraph ▸ h

end PlanarHom.ClosedMatrixFamily

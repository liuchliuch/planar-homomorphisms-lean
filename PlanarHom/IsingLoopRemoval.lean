import PlanarHom.IsingEvenSubgraph

/-! Exact removal of loop occurrences for constant-diagonal interactions. -/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph

variable {V E C R : Type*}

/-- Remove precisely the loop occurrences, preserving every original vertex
and every occurrence of every non-loop edge. -/
def withoutLoops (G : MultiGraph V E) :
    MultiGraph V {e : E // G.src e ≠ G.dst e} :=
  ⟨fun e => G.src e.1, fun e => G.dst e.1⟩

/-- The number of loop occurrences, including their multiplicities. -/
def loopCount [Fintype E] (G : MultiGraph V E) : ℕ :=
  Fintype.card {e : E // G.src e = G.dst e}

theorem withoutLoops_loopless (G : MultiGraph V E)
    (e : {e : E // G.src e ≠ G.dst e}) :
    G.withoutLoops.src e ≠ G.withoutLoops.dst e := e.2

/-- Every removed loop contributes exactly its common diagonal weight. -/
theorem partition_removeLoops [Fintype V] [Fintype E] [Fintype C]
    [CommSemiring R] (G : MultiGraph V E) (M : Matrix C C R) (w : C → R)
    (d : R) (hdiag : ∀ c, M c c = d) :
    G.partition M w = d ^ G.loopCount * G.withoutLoops.partition M w := by
  have he (σ : V → C) :
      (∏ e, M (σ (G.src e)) (σ (G.dst e))) =
        d ^ G.loopCount * ∏ e : {e : E // G.src e ≠ G.dst e},
          M (σ (G.src e.1)) (σ (G.dst e.1)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun e => G.src e = G.dst e)]
    have hl (e : {e : E // G.src e = G.dst e}) :
        M (σ (G.src e.1)) (σ (G.dst e.1)) = d := by
      rw [e.2, hdiag]
    simp only [hl, Finset.prod_const, Finset.card_univ, loopCount]
  simp only [partition, assignmentWeight, he, withoutLoops, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- The diagonal weight of `W ρ` is exactly one, so its loop factor is one. -/
theorem ising_partition_removeLoops [Fintype V] [Fintype E]
    (G : MultiGraph V E) (ρ : ℝ) :
    G.partition (Boolean.W ρ) (fun _ => 1) =
      G.withoutLoops.partition (Boolean.W ρ) (fun _ => 1) := by
  simpa using G.partition_removeLoops (Boolean.W ρ) (fun _ => 1) 1 (Boolean.W_diag ρ)

end PlanarHom.MultiGraph

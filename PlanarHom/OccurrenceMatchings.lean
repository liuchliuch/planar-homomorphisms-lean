import PlanarHom.IsingEvenSubgraph

/-! Perfect matchings of occurrence-labelled finite multigraphs. -/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph
variable {V E : Type*}

/-- A literal edge occurrence set covers every vertex exactly once. -/
def PerfectMatching (G : MultiGraph V E) (M : Finset E) : Prop :=
  ∀ v, G.selectedDegree M v = 1

/-- Weighted matching partition, permitting arbitrary signed real weights. -/
def perfectMatchingSum [Fintype E] (G : MultiGraph V E) (w : E → ℝ) : ℝ :=
  ∑ M : Finset E, if G.PerfectMatching M then ∏ e ∈ M, w e else 0

/-- Counting endpoints counts each occurrence twice, including a loop. -/
theorem sum_selectedDegree [Fintype V] (G : MultiGraph V E) (M : Finset E) :
    (∑ v, G.selectedDegree M v) = 2 * M.card := by
  simp only [selectedDegree]
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib, mul_comm]

theorem PerfectMatching.card_vertices [Fintype V] (G : MultiGraph V E)
    (M : Finset E) (hM : G.PerfectMatching M) :
    Fintype.card V = 2 * M.card := by
  have hv : ∀ v, G.selectedDegree M v = 1 := hM
  simpa only [hv, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
    G.sum_selectedDegree M

/-- A source loop cannot be selected by a perfect matching, since it covers
its vertex twice. Parallel edges remain separate eligible occurrences. -/
theorem PerfectMatching.no_loop (G : MultiGraph V E) (M : Finset E)
    (hM : G.PerfectMatching M) (e : E) (he : e ∈ M) : G.src e ≠ G.dst e := by
  intro hloop
  have hle := Finset.single_le_sum
    (fun d (_ : d ∈ M) => Nat.zero_le
      ((if G.src d = G.src e then 1 else 0) +
        (if G.dst d = G.src e then 1 else 0))) he
  change _ ≤ G.selectedDegree M (G.src e) at hle
  rw [hM] at hle
  simp [hloop] at hle

end PlanarHom.MultiGraph

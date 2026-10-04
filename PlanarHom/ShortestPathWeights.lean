import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import PlanarHom.PowerSumRigidity

/-!
# Matrix powers and weighted shortest paths

At the graph-distance degree, powers of a matrix supported on a graph and its
diagonal are sums of actual shortest-path edge products. The diagonal is
unrestricted: any diagonal step would leave too few steps to reach the other
endpoint. Entrywise positive integer powers raise each path weight to that
integer power.
-/

noncomputable section

open scoped BigOperators

namespace PlanarHom.ShortestPathWeights

variable {V : Type*}

/-- The genuine shortest walks in a graph. Every member is a simple path. -/
def ShortestPath (G : SimpleGraph V) (i j : V) :=
  {p : G.Walk i j // p.length = G.dist i j}

noncomputable instance shortestPathFintype [Fintype V] [DecidableEq V] (G : SimpleGraph V) (i j : V) :
    Fintype (ShortestPath G i j) := by
  classical
  unfold ShortestPath
  infer_instance

/-- Shortest walks have no repeated vertices. -/
theorem shortestPath_isPath (G : SimpleGraph V) {i j : V} (p : ShortestPath G i j) :
    p.val.IsPath := p.val.isPath_of_length_eq_dist p.property

/-- Equality with graph distance is equivalent to shortest length among all
actual walks with these endpoints. -/
theorem length_eq_dist_iff_minimal (G : SimpleGraph V) {i j : V} (p : G.Walk i j) :
    p.length = G.dist i j ↔ ∀ q : G.Walk i j, p.length ≤ q.length := by
  constructor
  · intro hp q
    rw [hp]
    exact SimpleGraph.dist_le q
  · intro hp
    obtain ⟨q, hq⟩ := (show G.Reachable i j from ⟨p⟩).exists_walk_length_eq_dist
    exact le_antisymm (hq ▸ hp q) (SimpleGraph.dist_le p)

/-- A connected graph has a shortest path between every pair of vertices. -/
theorem shortestPath_nonempty (G : SimpleGraph V) (hG : G.Connected) (i j : V) :
    Nonempty (ShortestPath G i j) := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i j
  exact ⟨⟨p, hp⟩⟩

/-- The product of matrix edge weights along an actual graph walk. -/
def walkWeight (K : Matrix V V ℝ) {G : SimpleGraph V} {i j : V} : G.Walk i j → ℝ
  | .nil => 1
  | @SimpleGraph.Walk.cons _ _ i k j _ p => K i k * walkWeight K p

@[simp] theorem walkWeight_nil (K : Matrix V V ℝ) (G : SimpleGraph V) (i : V) :
    walkWeight K (SimpleGraph.Walk.nil : G.Walk i i) = 1 := rfl

@[simp] theorem walkWeight_cons (K : Matrix V V ℝ) {G : SimpleGraph V}
    {i k j : V} (h : G.Adj i k) (p : G.Walk k j) :
    walkWeight K (p.cons h) = K i k * walkWeight K p := rfl

/-- Edgewise positivity gives positivity of every walk weight. -/
theorem walkWeight_pos (K : Matrix V V ℝ) (G : SimpleGraph V)
    (hedge : ∀ i j, G.Adj i j → 0 < K i j) {i j : V} (p : G.Walk i j) :
    0 < walkWeight K p := by
  induction p with
  | nil => exact zero_lt_one
  | @cons i k j hik p ih => exact mul_pos (hedge i k hik) ih

/-- Entrywise integer power, kept as a matrix so subsequent powers use matrix
multiplication rather than the pointwise function-space power instance. -/
def entrywisePow (K : Matrix V V ℝ) (s : ℕ) : Matrix V V ℝ :=
  fun i j => (K i j) ^ s

@[simp] theorem entrywisePow_apply (K : Matrix V V ℝ) (s : ℕ) (i j : V) :
    entrywisePow K s i j = (K i j) ^ s := rfl

/-- Entrywise powers commute with the product along a walk. -/
theorem walkWeight_entrywise_pow (K : Matrix V V ℝ) (s : ℕ)
    {G : SimpleGraph V} {i j : V} (p : G.Walk i j) :
    walkWeight (fun a b => (K a b) ^ s) p = (walkWeight K p) ^ s := by
  induction p with
  | nil => simp
  | @cons i k j hik p ih => simp only [walkWeight_cons, ih, mul_pow]

/-- The recursive weight is precisely the product of edge weights in the
walk's ordered list of directed edges. -/
theorem walkWeight_eq_prod_darts (K : Matrix V V ℝ) {G : SimpleGraph V}
    {i j : V} (p : G.Walk i j) :
    walkWeight K p = (p.darts.map (fun e => K e.fst e.snd)).prod := by
  induction p with
  | nil => simp
  | @cons i k j hik p ih =>
    simpa only [walkWeight_cons, SimpleGraph.Walk.darts_cons, List.map_cons,
      List.prod_cons] using congrArg (K i k * ·) ih

variable [Fintype V] [DecidableEq V]

/-- A nonzero coefficient in a matrix power supplies a graph walk of no greater
length, after discarding diagonal steps. -/
theorem exists_short_walk_of_pow_entry_ne_zero (K : Matrix V V ℝ) (G : SimpleGraph V)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0)
    (n : ℕ) {i j : V} (h : (K ^ n) i j ≠ 0) :
    ∃ p : G.Walk i j, p.length ≤ n := by
  induction n generalizing i j with
  | zero =>
    have hij : i = j := by
      by_contra hn
      exact h (by simp [hn])
    subst j
    exact ⟨.nil, le_rfl⟩
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨p, hp⟩ := ih (right_ne_zero_of_mul hk)
    by_cases hik : i = k
    · subst k
      exact ⟨p, hp.trans (Nat.le_succ n)⟩
    · have ha : G.Adj i k := by
        by_contra hn
        exact (left_ne_zero_of_mul hk) (hsupport i k hik hn)
      exact ⟨p.cons ha, by simpa using Nat.succ_le_succ hp⟩

/-- Coefficients below graph distance vanish, without sign assumptions. -/
theorem pow_entry_eq_zero_of_lt_dist (K : Matrix V V ℝ) (G : SimpleGraph V)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0)
    {n : ℕ} {i j : V} (hn : n < G.dist i j) : (K ^ n) i j = 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ := exists_short_walk_of_pow_entry_ne_zero K G hsupport n hne
  exact (not_le_of_gt hn) ((SimpleGraph.dist_le p).trans hp)

/-- Split a weighted walk at its first edge. -/
theorem sum_walkWeight_succ (K : Matrix V V ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (i j : V) :
    (∑ p ∈ G.finsetWalkLength (n + 1) i j, walkWeight K p) =
      ∑ k : G.neighborSet i, K i k *
        ∑ p ∈ G.finsetWalkLength n k j, walkWeight K p := by
  classical
  rw [SimpleGraph.finsetWalkLength, Finset.sum_biUnion]
  · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, walkWeight_cons,
      Finset.mul_sum]
  · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro p hp q hq hpq
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp hq
    obtain ⟨px, _, rfl⟩ := hp
    obtain ⟨py, _, rfl⟩ := hq
    cases hpq
    exact hxy rfl

/-- Up to graph distance, diagonal steps cannot contribute. The matrix-power
coefficient is exactly the sum over graph walks of that length. -/
theorem pow_entry_eq_sum_walkWeight_of_le_dist (K : Matrix V V ℝ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0)
    (n : ℕ) {i j : V} (hn : n ≤ G.dist i j) :
    (K ^ n) i j = ∑ p ∈ G.finsetWalkLength n i j, walkWeight K p := by
  classical
  induction n generalizing i j with
  | zero =>
    obtain rfl | hij := eq_or_ne i j
    · simp [SimpleGraph.finsetWalkLength]
    · simp [SimpleGraph.finsetWalkLength, hij]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, sum_walkWeight_succ]
    calc
      ∑ k, K i k * (K ^ n) k j =
          ∑ k ∈ Finset.univ.filter (G.Adj i), K i k * (K ^ n) k j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k _ hk
        have hnot : ¬G.Adj i k := by simpa only [Finset.mem_filter,
          Finset.mem_univ, true_and] using hk
        by_cases hik : i = k
        · subst k
          rw [pow_entry_eq_zero_of_lt_dist K G hsupport (Nat.lt_of_succ_le hn),
            mul_zero]
        · rw [hsupport i k hik hnot, zero_mul]
      _ = ∑ k : G.neighborSet i, K i k * (K ^ n) k j :=
        Finset.sum_subtype _ (by intro k; simp [SimpleGraph.mem_neighborSet]) _
      _ = ∑ k : G.neighborSet i, K i k *
          ∑ p ∈ G.finsetWalkLength n k j, walkWeight K p := by
        apply Finset.sum_congr rfl
        intro k _
        have ht := hG.dist_triangle (u := i) (v := k) (w := j)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr k.property] at ht
        have hd : n ≤ G.dist k j := by omega
        rw [ih hd]

/-- At distance degree, the matrix coefficient is the finite sum of the
products along all genuine shortest paths. Diagonal entries are unrestricted. -/
theorem pow_dist_eq_sum_shortestPathWeights (K : Matrix V V ℝ)
    (G : SimpleGraph V) (hG : G.Connected)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0) (i j : V) :
    (K ^ G.dist i j) i j = ∑ p : ShortestPath G i j, walkWeight K p.val := by
  classical
  rw [pow_entry_eq_sum_walkWeight_of_le_dist K G hG hsupport _ le_rfl]
  exact Finset.sum_subtype _ (fun _ => SimpleGraph.mem_finsetWalkLength_iff) _

/-- Applying a positive entrywise integer power raises each shortest-path
weight to that power. -/
theorem schur_pow_dist_eq_sum_shortestPathWeights_pow (K : Matrix V V ℝ)
    (G : SimpleGraph V) (hG : G.Connected)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0)
    (s : ℕ) (hs : 0 < s) (i j : V) :
    (entrywisePow K s ^ G.dist i j) i j =
      ∑ p : ShortestPath G i j, (walkWeight K p.val) ^ s := by
  have hsupport' : ∀ i j, i ≠ j → ¬G.Adj i j → (K i j) ^ s = 0 := by
    intro i j hij hnot
    rw [hsupport i j hij hnot, zero_pow (Nat.ne_of_gt hs)]
  calc
    _ = ∑ p : ShortestPath G i j,
        walkWeight (fun a b => (K a b) ^ s) p.val :=
      pow_dist_eq_sum_shortestPathWeights (entrywisePow K s) G hG hsupport' i j
    _ = _ := Finset.sum_congr rfl (fun p _ => walkWeight_entrywise_pow K s p.val)

/-- The coefficient comparison in the weighted-shortest-path argument implies
both the factorial path count and equality of all positive path weights. This
last step is finite algebra; the analytic coefficient identities are supplied
explicitly as the hypothesis `hpowers`. -/
theorem shortestPath_card_and_weights_of_even_power_identities
    (K : Matrix V V ℝ) (G : SimpleGraph V) (hG : G.Connected)
    (hsupport : ∀ i j, i ≠ j → ¬G.Adj i j → K i j = 0)
    (hedge : ∀ i j, G.Adj i j → 0 < K i j) (i j : V)
    (hpowers : ∀ s : ℕ, 0 < s → Even s →
      ((K ^ G.dist i j) i j / ((G.dist i j).factorial : ℝ)) ^ s =
        (entrywisePow K s ^ G.dist i j) i j / ((G.dist i j).factorial : ℝ)) :
    Fintype.card (ShortestPath G i j) = (G.dist i j).factorial ∧
      ∀ p q : ShortestPath G i j, walkWeight K p.val = walkWeight K q.val := by
  classical
  letI : Nonempty (ShortestPath G i j) := shortestPath_nonempty G hG i j
  have hmom : ∀ s : ℕ, 0 < s → Even s →
      ((∑ p : ShortestPath G i j, walkWeight K p.val) /
        ((G.dist i j).factorial : ℝ)) ^ s =
      (∑ p : ShortestPath G i j, (walkWeight K p.val) ^ s) /
        ((G.dist i j).factorial : ℝ) := by
    intro s hs heven
    have h := hpowers s hs heven
    rw [pow_dist_eq_sum_shortestPathWeights K G hG hsupport,
      schur_pow_dist_eq_sum_shortestPathWeights_pow K G hG hsupport s hs] at h
    exact h
  have hfac : 0 < ((G.dist i j).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (G.dist i j)
  obtain ⟨hweight, hcard⟩ := PowerSumRigidity.positive_even_power_sum_rigidity
    (fun p : ShortestPath G i j => walkWeight K p.val)
    ((G.dist i j).factorial : ℝ) (fun p => walkWeight_pos K G hedge p.val) hfac hmom
  refine ⟨by exact_mod_cast hcard, ?_⟩
  intro p q
  exact (hweight p).trans (hweight q).symm

end PlanarHom.ShortestPathWeights

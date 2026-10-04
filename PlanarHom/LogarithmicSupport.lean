import PlanarHom.KernelContinuation
import PlanarHom.PositivePowers

/-!
# Connectivity of the logarithmic support

The matrix exponential cannot create entries between distinct connected
components of the off-diagonal support of its argument. Consequently a
positive-definite matrix with connected support has connected logarithmic
support. This proves the connectedness assertion of Lemma 4.1, independently
of the still-open maximal-support and positive-logarithm construction.
-/

noncomputable section
set_option maxHeartbeats 800000

open scoped BigOperators Matrix.Norms.Operator

namespace PlanarHom.LogarithmicSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual loopless nonzero support of a real symmetric matrix. -/
def offDiagonalSupport (M : Matrix V V ℝ) (hM : M.IsHermitian) : SimpleGraph V where
  Adj i j := i ≠ j ∧ M i j ≠ 0
  symm := by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    have he : M j i = M i j := by simpa using hM.apply i j
    simpa only [he] using h.2
  loopless := fun i h => h.1 rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem offDiagonalSupport_adj (M : Matrix V V ℝ) (hM : M.IsHermitian) (i j : V) :
    (offDiagonalSupport M hM).Adj i j ↔ i ≠ j ∧ M i j ≠ 0 := Iff.rfl

/-- The paper's graph `R_H`, using the genuine spectral matrix logarithm. -/
def logSupport (H : Matrix V V ℝ) : SimpleGraph V :=
  offDiagonalSupport (EntropyCompletion.matrixLog H) IsSelfAdjoint.log

@[simp] theorem logSupport_adj (H : Matrix V V ℝ) (i j : V) :
    (logSupport H).Adj i j ↔ i ≠ j ∧ EntropyCompletion.matrixLog H i j ≠ 0 := Iff.rfl

omit [Fintype V] in
/-- A nonzero matrix entry either stays at a vertex or traverses a support edge. -/
theorem reachable_of_entry_ne_zero (M : Matrix V V ℝ) (hM : M.IsHermitian)
    {i j : V} (h : M i j ≠ 0) : (offDiagonalSupport M hM).Reachable i j := by
  by_cases hij : i = j
  · subst j; exact SimpleGraph.Reachable.rfl
  · exact (show (offDiagonalSupport M hM).Adj i j from ⟨hij, h⟩).reachable

/-- Every ordinary matrix power remains zero across distinct support components. -/
theorem pow_entry_eq_zero_of_not_reachable (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (n : ℕ) {i j : V} (h : ¬ (offDiagonalSupport M hM).Reachable i j) :
    (M ^ n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hij : i ≠ j := by rintro rfl; exact h SimpleGraph.Reachable.rfl
    simp [hij]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : (offDiagonalSupport M hM).Reachable i k
    · have hkj : M k j = 0 := by
        by_contra hne
        exact h (hik.trans (reachable_of_entry_ne_zero M hM hne))
      simp [hkj]
    · simp [ih hik]

/-- The exponential, too, is zero between distinct support components. -/
theorem exp_entry_eq_zero_of_not_reachable (M : Matrix V V ℝ) (hM : M.IsHermitian)
    {i j : V} (h : ¬ (offDiagonalSupport M hM).Reachable i j) :
    NormedSpace.exp ℝ M i j = 0 := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M).mapL
    (KernelContinuation.entryCLM i j)
  have hz : ∀ n : ℕ, (KernelContinuation.entryCLM i j)
      ((n.factorial : ℝ)⁻¹ • M ^ n) = 0 := by
    intro n
    change (n.factorial : ℝ)⁻¹ * (M ^ n) i j = 0
    rw [pow_entry_eq_zero_of_not_reachable M hM n h, mul_zero]
  have hzsum : HasSum (fun n : ℕ => (KernelContinuation.entryCLM i j)
      ((n.factorial : ℝ)⁻¹ • M ^ n)) 0 :=
    hasSum_zero.congr_fun hz
  exact hs.unique hzsum

/-- Every nonzero exponential entry joins vertices already connected in the
support of the exponent. This does not require nonnegative entries. -/
theorem reachable_of_exp_entry_ne_zero (M : Matrix V V ℝ) (hM : M.IsHermitian)
    {i j : V} (h : NormedSpace.exp ℝ M i j ≠ 0) :
    (offDiagonalSupport M hM).Reachable i j := by
  by_contra hn
  exact h (exp_entry_eq_zero_of_not_reachable M hM hn)

/-- A nonzero entry of a positive-definite matrix connects vertices in its
logarithmic support. -/
theorem logSupport_reachable_of_entry_ne_zero {H : Matrix V V ℝ} (hH : H.PosDef)
    {i j : V} (hij : H i j ≠ 0) : (logSupport H).Reachable i j := by
  apply reachable_of_exp_entry_ne_zero (EntropyCompletion.matrixLog H) IsSelfAdjoint.log
  simpa only [KernelContinuation.exp_matrixLog hH] using hij

/-- Connectivity transfers from any graph of nonzero entries to logarithmic support. -/
theorem logSupport_connected_of_connected_graph {H : Matrix V V ℝ} (hH : H.PosDef)
    (G : SimpleGraph V) (hG : G.Connected) (he : ∀ i j, G.Adj i j → H i j ≠ 0) :
    (logSupport H).Connected := by
  letI : Nonempty V := hG.nonempty
  refine ⟨?_⟩
  intro i j
  obtain ⟨p⟩ := hG i j
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons a b c hab p ih =>
    exact (logSupport_reachable_of_entry_ne_zero hH (he a b hab)).trans ih

/-- The connectedness assertion in Lemma 4.1: a positive-definite matrix with
connected nonzero support has connected logarithmic support. -/
theorem logSupport_connected {H : Matrix V V ℝ} (hH : H.PosDef)
    (hc : (offDiagonalSupport H hH.1).Connected) : (logSupport H).Connected :=
  logSupport_connected_of_connected_graph hH _ hc (fun _ _ h => h.2)

/-- Positive support is the equivalent source convention for entrywise
nonnegative matrices; this corollary even permits arbitrary diagonal signs. -/
theorem logSupport_connected_of_positiveSupport {H : Matrix V V ℝ} (hH : H.PosDef)
    (hs : ∀ i j, H i j = H j i)
    (hc : (PositivePowers.positiveSupport H hs).Connected) : (logSupport H).Connected :=
  logSupport_connected_of_connected_graph hH _ hc (fun _ _ h => ne_of_gt h.2)

/-- A nonzero entry in the n-th power is supported by a walk of length at most n.
Diagonal steps may be discarded; no entrywise sign condition is required. -/
theorem exists_short_walk_of_pow_entry_ne_zero (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (n : ℕ) {i j : V} (h : (M ^ n) i j ≠ 0) :
    ∃ p : (offDiagonalSupport M hM).Walk i j, p.length ≤ n := by
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
    · have ha : (offDiagonalSupport M hM).Adj i k := ⟨hik, left_ne_zero_of_mul hk⟩
      exact ⟨p.cons ha, by simpa using Nat.succ_le_succ hp⟩

/-- All matrix-power coefficients below graph distance vanish. -/
theorem pow_entry_eq_zero_of_lt_dist (M : Matrix V V ℝ) (hM : M.IsHermitian)
    {n : ℕ} {i j : V} (hn : n < (offDiagonalSupport M hM).dist i j) :
    (M ^ n) i j = 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ := exists_short_walk_of_pow_entry_ne_zero M hM n hne
  exact (not_le_of_gt hn) ((SimpleGraph.dist_le p).trans hp)

/-- At or below the shortest-path degree, positive off-diagonal support suffices
for nonnegative power coefficients even with arbitrary real diagonal entries. -/
theorem pow_entry_nonneg_of_le_dist (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (hG : (offDiagonalSupport M hM).Connected)
    (hedge : ∀ i j, (offDiagonalSupport M hM).Adj i j → 0 < M i j)
    (n : ℕ) {i j : V} (hn : n ≤ (offDiagonalSupport M hM).dist i j) :
    0 ≤ (M ^ n) i j := by
  induction n generalizing i j with
  | zero =>
    by_cases hij : i = j <;> simp [hij]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro k _
    by_cases hik : i = k
    · subst k
      rw [pow_entry_eq_zero_of_lt_dist M hM (Nat.lt_of_succ_le hn), mul_zero]
    · by_cases hm : M i k = 0
      · simp [hm]
      · have ha : (offDiagonalSupport M hM).Adj i k := ⟨hik, hm⟩
        have ht := hG.dist_triangle (u := i) (v := k) (w := j)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha] at ht
        have hd : n ≤ (offDiagonalSupport M hM).dist k j := by omega
        exact mul_nonneg (hedge i k ha).le (ih hd)

/-- Every shortest support walk contributes a strictly positive coefficient;
no diagonal factor can occur at this first nonzero degree. -/
theorem pow_entry_pos_of_shortest_walk (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (hG : (offDiagonalSupport M hM).Connected)
    (hedge : ∀ i j, (offDiagonalSupport M hM).Adj i j → 0 < M i j)
    {i j : V} (p : (offDiagonalSupport M hM).Walk i j)
    (hp : p.length = (offDiagonalSupport M hM).dist i j) :
    0 < (M ^ p.length) i j := by
  induction p with
  | nil => simp
  | @cons i k j hik p ih =>
    have ht := hG.dist_triangle (u := i) (v := k) (w := j)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hik] at ht
    have hle := SimpleGraph.dist_le p
    have he : p.length = (offDiagonalSupport M hM).dist k j := by
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
    have hpos := mul_pos (hedge i k hik) (ih he)
    rw [SimpleGraph.Walk.length_cons, pow_succ', Matrix.mul_apply]
    apply lt_of_lt_of_le hpos
    refine Finset.single_le_sum (f := fun l : V => M i l * (M ^ p.length) l j)
      ?_ (Finset.mem_univ k)
    intro l _
    change 0 ≤ M i l * (M ^ p.length) l j
    by_cases hil : i = l
    · subst l
      have hl : p.length < (offDiagonalSupport M hM).dist i j := by
        simpa only [SimpleGraph.Walk.length_cons] using hp ▸ Nat.lt_succ_self p.length
      rw [pow_entry_eq_zero_of_lt_dist M hM hl, mul_zero]
    · by_cases hm : M i l = 0
      · simp [hm]
      · have ha : (offDiagonalSupport M hM).Adj i l := ⟨hil, hm⟩
        have ht := hG.dist_triangle (u := i) (v := l) (w := j)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha] at ht
        have hd : p.length ≤ (offDiagonalSupport M hM).dist l j := by
          simp only [SimpleGraph.Walk.length_cons] at hp
          omega
        exact mul_nonneg (hedge i l ha).le (pow_entry_nonneg_of_le_dist M hM hG hedge _ hd)

/-- The leading matrix-exponential coefficient used in Lemma 4.2 is positive:
`(L ^ d(i,j)) i j > 0`. All smaller coefficients vanish by the preceding theorem. -/
theorem pow_distance_entry_pos (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (hG : (offDiagonalSupport M hM).Connected)
    (hedge : ∀ i j, (offDiagonalSupport M hM).Adj i j → 0 < M i j)
    (i j : V) : 0 < (M ^ (offDiagonalSupport M hM).dist i j) i j := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i j
  simpa only [hp] using pow_entry_pos_of_shortest_walk M hM hG hedge p hp

end PlanarHom.LogarithmicSupport

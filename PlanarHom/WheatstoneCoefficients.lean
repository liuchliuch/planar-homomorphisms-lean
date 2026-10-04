import PlanarHom.CartesianGeometry
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Exact Wheatstone gadget polynomials

The two internal colors are summed explicitly. Coefficients count actual
monomials in the graph-distance kernel, with no asymptotic remainder assumed.
These calculations support Lemma 4.4; they do not assert gadget availability.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PlanarHom.WheatstoneCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Length of the walk forced through one internal color. -/
def through (G : SimpleGraph V) (i j a : V) : ℕ := G.dist i a + G.dist a j

/-- Exponent of one actual Wheatstone internal-color assignment. -/
def exponent (G : SimpleGraph V) (i j a b : V) : ℕ :=
  through G i j a + through G i j b + G.dist a b

/-- The exact polynomial of the five-edge Wheatstone gadget. -/
def polynomial (G : SimpleGraph V) (i j : V) : Polynomial ℝ :=
  ∑ a : V, ∑ b : V, Polynomial.X ^ exponent G i j a b

omit [DecidableEq V] in
/-- Evaluation agrees with the actual five distance-kernel factors. -/
theorem polynomial_eval (G : SimpleGraph V) (i j : V) (x : ℝ) :
    (polynomial G i j).eval x = ∑ a : V, ∑ b : V,
      EntropyCompletion.distanceKernel G x i a * EntropyCompletion.distanceKernel G x a j *
      EntropyCompletion.distanceKernel G x i b * EntropyCompletion.distanceKernel G x b j *
      EntropyCompletion.distanceKernel G x a b := by
  simp [polynomial, Polynomial.eval_finset_sum, exponent, through,
    EntropyCompletion.distanceKernel, pow_add, mul_assoc]

omit [Fintype V] [DecidableEq V] in
/-- Every forced-through path is at least the graph distance. -/
theorem dist_le_through (G : SimpleGraph V) (hc : G.Connected) (i j a : V) :
    G.dist i j ≤ through G i j a := hc.dist_triangle

omit [Fintype V] in
/-- For a distance-two pair, the through-length equals two exactly at the two
terminals and their common neighbors. -/
theorem through_eq_two_iff (G : SimpleGraph V) (hc : G.Connected) {i j a : V}
    (hd : G.dist i j = 2) :
    through G i j a = 2 ↔ a = i ∨ a = j ∨ (G.Adj i a ∧ G.Adj j a) := by
  constructor
  · intro h
    by_cases hai : a = i
    · exact Or.inl hai
    by_cases haj : a = j
    · exact Or.inr (Or.inl haj)
    have hi : 0 < G.dist i a := hc.pos_dist_of_ne (Ne.symm hai)
    have hj : 0 < G.dist a j := hc.pos_dist_of_ne haj
    have ha : G.dist i a = 1 := by unfold through at h; omega
    have hb : G.dist a j = 1 := by unfold through at h; omega
    exact Or.inr (Or.inr ⟨SimpleGraph.dist_eq_one_iff_adj.mp ha,
      (SimpleGraph.dist_eq_one_iff_adj.mp hb).symm⟩)
  · rintro (rfl | rfl | ⟨hia, hja⟩)
    · simp [through, hd]
    · simp [through, hd]
    · simp only [through, SimpleGraph.dist_eq_one_iff_adj.mpr hia,
        SimpleGraph.dist_eq_one_iff_adj.mpr hja.symm]

omit [Fintype V] [DecidableEq V] in
/-- The degree-four assignments are precisely coincident geodesic colors. -/
theorem exponent_eq_four_iff (G : SimpleGraph V) (hc : G.Connected) {i j a b : V}
    (hd : G.dist i j = 2) :
    exponent G i j a b = 4 ↔ a = b ∧ through G i j a = 2 := by
  have ha : 2 ≤ through G i j a := hd ▸ dist_le_through G hc i j a
  have hb : 2 ≤ through G i j b := hd ▸ dist_le_through G hc i j b
  constructor
  · intro h
    have hz : G.dist a b = 0 := by unfold exponent at h; omega
    exact ⟨hc.dist_eq_zero_iff.mp hz, by unfold exponent at h; omega⟩
  · rintro ⟨rfl, h⟩
    simp [exponent, h]

omit [Fintype V] [DecidableEq V] in
/-- The degree-five assignments are precisely ordered adjacent geodesic colors. -/
theorem exponent_eq_five_iff (G : SimpleGraph V) (hc : G.Connected) {i j a b : V}
    (hd : G.dist i j = 2) :
    exponent G i j a b = 5 ↔
      through G i j a = 2 ∧ through G i j b = 2 ∧ G.Adj a b := by
  have ha : 2 ≤ through G i j a := hd ▸ dist_le_through G hc i j a
  have hb : 2 ≤ through G i j b := hd ▸ dist_le_through G hc i j b
  constructor
  · intro h
    have hab : a ≠ b := by
      rintro rfl
      simp only [exponent, SimpleGraph.dist_self, add_zero] at h
      omega
    have hp := hc.pos_dist_of_ne hab
    have hz : G.dist a b = 1 := by unfold exponent at h; omega
    exact ⟨by unfold exponent at h; omega, by unfold exponent at h; omega,
      SimpleGraph.dist_eq_one_iff_adj.mp hz⟩
  · rintro ⟨ha, hb, hab⟩
    simp [exponent, ha, hb, SimpleGraph.dist_eq_one_iff_adj.mpr hab]

/-- The finite set of colors lying on a shortest terminal-to-terminal walk. -/
def geodesicColors (G : SimpleGraph V) (i j : V) : Finset V :=
  Finset.univ.filter (fun a => through G i j a = G.dist i j)

/-- Exact degree-four coefficient, before using the two-common-neighbor hypothesis. -/
theorem coeff_four (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hd : G.dist i j = 2) :
    (polynomial G i j).coeff 4 = ((geodesicColors G i j).card : ℝ) := by
  classical
  rw [geodesicColors, hd, ← Finset.sum_boole (R := ℝ)]
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ b, (4 = exponent G i j a b) ↔ a = b ∧ through G i j a = 2 :=
    fun b => eq_comm.trans (exponent_eq_four_iff G hc hd)
  simp_rw [he]
  by_cases ha : through G i j a = 2 <;> simp [ha]

omit [DecidableEq V] in
/-- Exact degree-five coefficient: the number of oriented edges among geodesic colors. -/
theorem coeff_five (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hd : G.dist i j = 2) :
    (polynomial G i j).coeff 5 =
      ∑ a ∈ geodesicColors G i j, ∑ b ∈ geodesicColors G i j,
        if G.Adj a b then (1 : ℝ) else 0 := by
  classical
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    geodesicColors, hd, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ b, (5 = exponent G i j a b) ↔
      through G i j a = 2 ∧ through G i j b = 2 ∧ G.Adj a b :=
    fun b => eq_comm.trans (exponent_eq_five_iff G hc hd)
  simp_rw [he]
  by_cases ha : through G i j a = 2
  · simp only [ha, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : through G i j b = 2 <;> simp [hb]
  · simp [ha]

/-- With exactly two common neighbors, the geodesic set has exactly four colors. -/
theorem geodesicColors_eq_four (G : SimpleGraph V) (hc : G.Connected) {i j u v : V}
    (hd : G.dist i j = 2)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    geodesicColors G i j = {i, j, u, v} := by
  classical
  ext a
  simp only [geodesicColors, Finset.mem_filter, Finset.mem_univ, true_and, hd,
    through_eq_two_iff G hc hd, Finset.mem_insert, Finset.mem_singleton, hcommon]

/-- The precise degree-four coefficient in Lemma 4.4 is four. -/
theorem coeff_four_eq_four (G : SimpleGraph V) (hc : G.Connected) {i j u v : V}
    (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    (polynomial G i j).coeff 4 = 4 := by
  classical
  have hiu := ((hcommon u).mpr (Or.inl rfl)).1
  have hju := ((hcommon u).mpr (Or.inl rfl)).2
  have hiv := ((hcommon v).mpr (Or.inr rfl)).1
  have hjv := ((hcommon v).mpr (Or.inr rfl)).2
  have hij : i ≠ j := by
    intro h
    rw [h, SimpleGraph.dist_self] at hd
    omega
  rw [coeff_four G hc hd, geodesicColors_eq_four G hc hd hcommon]
  simp [hij, hiu.ne, hiv.ne, hju.ne, hjv.ne, huv]

/-- The precise degree-five coefficient in Lemma 4.4 is eight, plus two if
and only if the two common neighbors are adjacent. -/
theorem coeff_five_eq_eight_add (G : SimpleGraph V) (hc : G.Connected) {i j u v : V}
    (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    (polynomial G i j).coeff 5 = 8 + if G.Adj u v then 2 else 0 := by
  classical
  have hiu := ((hcommon u).mpr (Or.inl rfl)).1
  have hju := ((hcommon u).mpr (Or.inl rfl)).2
  have hiv := ((hcommon v).mpr (Or.inr rfl)).1
  have hjv := ((hcommon v).mpr (Or.inr rfl)).2
  have hij : i ≠ j := by
    intro h
    rw [h, SimpleGraph.dist_self] at hd
    omega
  have hnij : ¬ G.Adj i j := by
    intro h
    have := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  rw [coeff_five G hc hd, geodesicColors_eq_four G hc hd hcommon]
  by_cases ha : G.Adj u v <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hij, hiu.ne, hiv.ne,
      hju.ne, hjv.ne, huv, hiu, hju, hiv, hjv, hiu.symm, hju.symm, hiv.symm,
      hjv.symm, hnij, G.adj_comm j i, G.adj_comm v u, ha] <;> norm_num

end PlanarHom.WheatstoneCoefficients

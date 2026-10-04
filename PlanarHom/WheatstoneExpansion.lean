import PlanarHom.WheatstoneCoefficients

/-!
# Low-order coefficients of the Wheatstone matrix

Exact diagonal and edge coefficients, and coefficient vanishing below twice
graph distance. These are the polynomial inputs to the analytic logarithm
comparison in Lemma 4.4.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace PlanarHom.WheatstoneCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Every Wheatstone exponent is at least twice the terminal distance. -/
theorem twice_dist_le_exponent (G : SimpleGraph V) (hc : G.Connected) (i j a b : V) :
    2 * G.dist i j ≤ exponent G i j a b := by
  have ha := dist_le_through G hc i j a
  have hb := dist_le_through G hc i j b
  unfold exponent
  omega

omit [DecidableEq V] in
/-- All coefficients below twice the terminal distance vanish exactly. -/
theorem coeff_eq_zero_of_lt_twice_dist (G : SimpleGraph V) (hc : G.Connected)
    (i j : V) {n : ℕ} (hn : n < 2 * G.dist i j) : (polynomial G i j).coeff n = 0 := by
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  have he := twice_dist_le_exponent G hc i j a b
  rw [if_neg (by omega)]

omit [Fintype V] [DecidableEq V] in
/-- The least possible degree comes from a coincident geodesic color. -/
theorem exponent_eq_twice_dist_iff (G : SimpleGraph V) (hc : G.Connected) (i j a b : V) :
    exponent G i j a b = 2 * G.dist i j ↔ a = b ∧ through G i j a = G.dist i j := by
  have ha := dist_le_through G hc i j a
  have hb := dist_le_through G hc i j b
  constructor
  · intro h
    have hz : G.dist a b = 0 := by unfold exponent at h; omega
    exact ⟨hc.dist_eq_zero_iff.mp hz, by unfold exponent at h; omega⟩
  · rintro ⟨rfl, h⟩
    simp only [exponent, h, SimpleGraph.dist_self]
    omega

omit [Fintype V] [DecidableEq V] in
/-- The next degree comes from an ordered adjacent pair of geodesic colors. -/
theorem exponent_eq_twice_dist_add_one_iff (G : SimpleGraph V) (hc : G.Connected)
    (i j a b : V) :
    exponent G i j a b = 2 * G.dist i j + 1 ↔
      through G i j a = G.dist i j ∧ through G i j b = G.dist i j ∧ G.Adj a b := by
  have ha := dist_le_through G hc i j a
  have hb := dist_le_through G hc i j b
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
    simp only [exponent, ha, hb, SimpleGraph.dist_eq_one_iff_adj.mpr hab]
    omega

/-- The first coefficient counts geodesic colors. -/
theorem coeff_twice_dist (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (polynomial G i j).coeff (2 * G.dist i j) = ((geodesicColors G i j).card : ℝ) := by
  rw [geodesicColors, ← Finset.sum_boole (R := ℝ)]
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ b, (2 * G.dist i j = exponent G i j a b) ↔
      a = b ∧ through G i j a = G.dist i j :=
    fun b => eq_comm.trans (exponent_eq_twice_dist_iff G hc i j a b)
  simp_rw [he]
  by_cases ha : through G i j a = G.dist i j <;> simp [ha]

omit [DecidableEq V] in
/-- The next coefficient counts oriented geodesic edges. -/
theorem coeff_twice_dist_add_one (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (polynomial G i j).coeff (2 * G.dist i j + 1) =
      ∑ a ∈ geodesicColors G i j, ∑ b ∈ geodesicColors G i j,
        if G.Adj a b then (1 : ℝ) else 0 := by
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    geodesicColors, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ b, (2 * G.dist i j + 1 = exponent G i j a b) ↔
      through G i j a = G.dist i j ∧ through G i j b = G.dist i j ∧ G.Adj a b :=
    fun b => eq_comm.trans (exponent_eq_twice_dist_add_one_iff G hc i j a b)
  simp_rw [he]
  by_cases ha : through G i j a = G.dist i j
  · simp only [ha, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : through G i j b = G.dist i j <;> simp [hb]
  · simp [ha]

/-- An edge has only its endpoints as geodesic colors. -/
theorem geodesicColors_edge (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hij : G.Adj i j) : geodesicColors G i j = {i, j} := by
  ext a
  simp only [geodesicColors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hij]
  constructor
  · intro ha
    have hz : G.dist i a = 0 ∨ G.dist a j = 0 := by unfold through at ha; omega
    exact hz.elim (fun h => Or.inl (hc.dist_eq_zero_iff.mp h).symm)
      (fun h => Or.inr (hc.dist_eq_zero_iff.mp h))
  · rintro (rfl | rfl) <;>
      simp [through, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hij]

/-- On every support edge the exact degree-two coefficient is two. -/
theorem edge_coeff_two (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hij : G.Adj i j) : (polynomial G i j).coeff 2 = 2 := by
  have h := coeff_twice_dist G hc i j
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hij, geodesicColors_edge G hc hij] at h
  simpa [hij.ne] using h

/-- On every support edge the exact degree-three coefficient is two. -/
theorem edge_coeff_three (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hij : G.Adj i j) : (polynomial G i j).coeff 3 = 2 := by
  have h := coeff_twice_dist_add_one G hc i j
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hij, geodesicColors_edge G hc hij] at h
  norm_num [Finset.filter_insert, Finset.filter_singleton, hij.ne, hij, hij.symm] at h ⊢
  exact h

/-- On the diagonal, the only geodesic color is the terminal itself. -/
theorem geodesicColors_self (G : SimpleGraph V) (hc : G.Connected) (i : V) :
    geodesicColors G i i = {i} := by
  ext a
  simp only [geodesicColors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, SimpleGraph.dist_self, through, Nat.add_eq_zero_iff,
    hc.dist_eq_zero_iff]
  tauto

/-- The constant coefficient on the diagonal is one. -/
theorem diagonal_coeff_zero (G : SimpleGraph V) (hc : G.Connected) (i : V) :
    (polynomial G i i).coeff 0 = 1 := by
  have h := coeff_twice_dist G hc i i
  simpa [SimpleGraph.dist_self, geodesicColors_self G hc] using h

omit [Fintype V] [DecidableEq V] in
/-- Every nonconstant diagonal assignment has degree at least three. -/
theorem diagonal_exponent_zero_or_three_le (G : SimpleGraph V) (hc : G.Connected)
    (i a b : V) : exponent G i i a b = 0 ∨ 3 ≤ exponent G i i a b := by
  have ha := G.dist_comm (u := a) (v := i)
  have hb := G.dist_comm (u := b) (v := i)
  by_cases hai : a = i
  · subst a
    by_cases hbi : b = i
    · subst b; left; simp [exponent, through, SimpleGraph.dist_self]
    · right
      have hp := hc.pos_dist_of_ne (Ne.symm hbi)
      simp only [exponent, through, SimpleGraph.dist_self, zero_add, add_zero]
      omega
  · by_cases hbi : b = i
    · subst b
      right
      have hp := hc.pos_dist_of_ne (Ne.symm hai)
      simp only [exponent, through, SimpleGraph.dist_self, add_zero]
      omega
    · right
      have hp := hc.pos_dist_of_ne (Ne.symm hai)
      have hq := hc.pos_dist_of_ne (Ne.symm hbi)
      unfold exponent through
      omega

omit [DecidableEq V] in
/-- The diagonal degree-one and degree-two coefficients vanish. -/
theorem diagonal_coeff_one_two (G : SimpleGraph V) (hc : G.Connected) (i : V)
    {n : ℕ} (hn : n = 1 ∨ n = 2) : (polynomial G i i).coeff n = 0 := by
  simp only [polynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  have he := diagonal_exponent_zero_or_three_le G hc i a b
  rw [if_neg (by omega)]

/-- All constant coefficients form exactly the identity matrix. -/
theorem coeff_zero (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (polynomial G i j).coeff 0 = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j; simp [diagonal_coeff_zero G hc]
  · rw [if_neg hij]
    apply coeff_eq_zero_of_lt_twice_dist G hc
    have hp := hc.pos_dist_of_ne hij
    omega

/-- The whole degree-one matrix is zero. -/
theorem coeff_one (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (polynomial G i j).coeff 1 = 0 := by
  by_cases hij : i = j
  · subst j; exact diagonal_coeff_one_two G hc i (Or.inl rfl)
  · apply coeff_eq_zero_of_lt_twice_dist G hc
    have hp := hc.pos_dist_of_ne hij
    omega

/-- The degree-two matrix is twice the simple-graph adjacency matrix. -/
theorem coeff_two (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (polynomial G i j).coeff 2 = if G.Adj i j then 2 else 0 := by
  by_cases h : G.Adj i j
  · rw [if_pos h]; exact edge_coeff_two G hc h
  · rw [if_neg h]
    by_cases hij : i = j
    · subst j; exact diagonal_coeff_one_two G hc i (Or.inr rfl)
    · apply coeff_eq_zero_of_lt_twice_dist G hc
      have hp := hc.one_lt_dist_of_ne_of_not_adj hij h
      omega

/-- Away from the diagonal, the degree-three matrix is also twice adjacency. -/
theorem offDiagonal_coeff_three (G : SimpleGraph V) (hc : G.Connected) {i j : V}
    (hij : i ≠ j) : (polynomial G i j).coeff 3 = if G.Adj i j then 2 else 0 := by
  by_cases h : G.Adj i j
  · rw [if_pos h]; exact edge_coeff_three G hc h
  · rw [if_neg h]
    apply coeff_eq_zero_of_lt_twice_dist G hc
    have hp := hc.one_lt_dist_of_ne_of_not_adj hij h
    omega

/-- The exact polynomial matrix corresponding to the Wheatstone signature. -/
def polynomialMatrix (G : SimpleGraph V) : Matrix V V (Polynomial ℝ) := polynomial G

/-- Its perturbation from the identity. -/
def perturbationPolynomial (G : SimpleGraph V) : Matrix V V (Polynomial ℝ) :=
  polynomialMatrix G - 1

/-- Subtracting the identity removes every constant term. -/
theorem perturbation_coeff_zero (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (perturbationPolynomial G i j).coeff 0 = 0 := by
  by_cases hij : i = j <;>
    simp [perturbationPolynomial, polynomialMatrix, coeff_zero G hc, hij]

/-- Positive-degree coefficients are unchanged by subtracting the identity. -/
theorem perturbation_coeff_pos (G : SimpleGraph V) (i j : V) {n : ℕ} (hn : n ≠ 0) :
    (perturbationPolynomial G i j).coeff n = (polynomial G i j).coeff n := by
  by_cases hij : i = j <;>
    simp [perturbationPolynomial, polynomialMatrix, hij, Polynomial.coeff_one, hn]

/-- A reusable exact fourth coefficient of a product of order-two polynomials. -/
theorem mul_coeff_four_of_order_two (p q : Polynomial ℝ)
    (hp0 : p.coeff 0 = 0) (hp1 : p.coeff 1 = 0)
    (hq0 : q.coeff 0 = 0) (hq1 : q.coeff 1 = 0) :
    (p * q).coeff 4 = p.coeff 2 * q.coeff 2 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ, hp0, hp1, hq0, hq1]

/-- A reusable exact fifth coefficient of a product of order-two polynomials. -/
theorem mul_coeff_five_of_order_two (p q : Polynomial ℝ)
    (hp0 : p.coeff 0 = 0) (hp1 : p.coeff 1 = 0)
    (hq0 : q.coeff 0 = 0) (hq1 : q.coeff 1 = 0) :
    (p * q).coeff 5 = p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ, hp0, hp1, hq0, hq1]

/-- The perturbation has no degree-one coefficients. -/
theorem perturbation_coeff_one (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    (perturbationPolynomial G i j).coeff 1 = 0 := by
  rw [perturbation_coeff_pos G i j (by decide), coeff_one G hc]

/-- Summing the indicator of two distinct colors gives two equal contributions. -/
theorem sum_two_color_indicator (u v : V) (huv : u ≠ v) (a : ℝ) :
    (∑ k : V, if k = u ∨ k = v then a else 0) = a + a := by
  have he : ∀ k : V, (if k = u ∨ k = v then a else 0) =
      (if k = u then a else 0) + (if k = v then a else 0) := by
    intro k
    by_cases hku : k = u
    · subst k; simp [huv]
    · by_cases hkv : k = v
      · subst k; simp [Ne.symm huv]
      · simp [hku, hkv]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

/-- The degree-four coefficient of `Q²` at a distance-two pair is eight. -/
theorem perturbation_square_coeff_four (G : SimpleGraph V) (hc : G.Connected)
    {i j u v : V} (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    ((perturbationPolynomial G ^ 2) i j).coeff 4 = 8 := by
  rw [pow_two, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  have he : ∀ k : V,
      ((perturbationPolynomial G i k) * (perturbationPolynomial G k j)).coeff 4 =
      if k = u ∨ k = v then 4 else 0 := by
    intro k
    rw [mul_coeff_four_of_order_two _ _ (perturbation_coeff_zero G hc i k)
      (perturbation_coeff_one G hc i k) (perturbation_coeff_zero G hc k j)
      (perturbation_coeff_one G hc k j),
      perturbation_coeff_pos G i k (by decide), perturbation_coeff_pos G k j (by decide),
      coeff_two G hc, coeff_two G hc]
    simp only [← hcommon k]
    by_cases ha : G.Adj i k <;> by_cases hb : G.Adj j k <;>
      norm_num [ha, hb, G.adj_comm k j]
  simp_rw [he]
  norm_num [sum_two_color_indicator u v huv]

/-- The degree-five coefficient of `Q²` at a distance-two pair is sixteen. -/
theorem perturbation_square_coeff_five (G : SimpleGraph V) (hc : G.Connected)
    {i j u v : V} (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v) :
    ((perturbationPolynomial G ^ 2) i j).coeff 5 = 16 := by
  have hnij : ¬ G.Adj i j := by
    intro h
    have := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  rw [pow_two, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  have he : ∀ k : V,
      ((perturbationPolynomial G i k) * (perturbationPolynomial G k j)).coeff 5 =
      if k = u ∨ k = v then 8 else 0 := by
    intro k
    rw [mul_coeff_five_of_order_two _ _ (perturbation_coeff_zero G hc i k)
      (perturbation_coeff_one G hc i k) (perturbation_coeff_zero G hc k j)
      (perturbation_coeff_one G hc k j),
      perturbation_coeff_pos G i k (by decide), perturbation_coeff_pos G k j (by decide),
      perturbation_coeff_pos G i k (by decide), perturbation_coeff_pos G k j (by decide),
      coeff_two G hc, coeff_two G hc]
    simp only [← hcommon k]
    by_cases hik : i = k
    · subst k
      simp [hnij]
    by_cases hkj : k = j
    · subst k
      simp [hnij]
    rw [offDiagonal_coeff_three G hc hik, offDiagonal_coeff_three G hc hkj]
    by_cases ha : G.Adj i k <;> by_cases hb : G.Adj j k <;>
      norm_num [ha, hb, G.adj_comm k j]
  simp_rw [he]
  norm_num [sum_two_color_indicator u v huv]

/-- A product of two order-two polynomials has no coefficient below degree four. -/
theorem mul_coeff_eq_zero_of_order_two (p q : Polynomial ℝ)
    (hp : ∀ k < 2, p.coeff k = 0) (hq : ∀ k < 2, q.coeff k = 0)
    {n : ℕ} (hn : n < 4) : (p * q).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  have he := Finset.mem_antidiagonal.mp ha
  have hlo : a.1 < 2 ∨ a.2 < 2 := by omega
  rcases hlo with h | h
  · rw [hp _ h, zero_mul]
  · rw [hq _ h, mul_zero]

/-- The actual perturbation begins at degree two. -/
theorem perturbation_coeff_lt_two (G : SimpleGraph V) (hc : G.Connected) (i j : V)
    (k : ℕ) (hk : k < 2) : (perturbationPolynomial G i j).coeff k = 0 := by
  interval_cases k
  · exact perturbation_coeff_zero G hc i j
  · exact perturbation_coeff_one G hc i j

/-- Every entry of the squared perturbation begins at degree four. -/
theorem perturbation_square_coeff_lt_four (G : SimpleGraph V) (hc : G.Connected)
    (i j : V) (k : ℕ) (hk : k < 4) :
    ((perturbationPolynomial G ^ 2) i j).coeff k = 0 := by
  rw [pow_two, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro a _
  exact mul_coeff_eq_zero_of_order_two _ _ (perturbation_coeff_lt_two G hc i a)
    (perturbation_coeff_lt_two G hc a j) hk

omit [Fintype V] [DecidableEq V] in
/-- Reversing the terminals does not alter a forced-through length. -/
theorem through_comm (G : SimpleGraph V) (i j a : V) :
    through G i j a = through G j i a := by
  unfold through
  rw [G.dist_comm (u := i) (v := a), G.dist_comm (u := a) (v := j)]
  omega

omit [DecidableEq V] in
/-- The exact polynomial signature is symmetric. -/
theorem polynomial_symm (G : SimpleGraph V) (i j : V) : polynomial G i j = polynomial G j i := by
  unfold polynomial exponent
  simp only [through_comm G i j]

end PlanarHom.WheatstoneCoefficients

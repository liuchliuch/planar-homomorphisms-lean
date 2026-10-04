import PlanarHom.CanonicalCoordinateHeights
import PlanarHom.AlphabetCoordinateCertificates

/-! Polynomial output-size bounds for arbitrary field values materialized in a list input. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.MaterializedFieldHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

/-- Each actual element word is charged by its containing list's exact codec. -/
theorem element_length_le_list {A : Type} (e : BitEncoding A) (xs : List A) {x : A} (hx : x ∈ xs) :
    (e.encode x).length ≤ (e.list.encode xs).length := by
  have hs : (e.encode x).length ≤ (xs.map (fun y => (e.encode y).length)).sum := by
    induction xs with
    | nil => simp at hx
    | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hm
      · simp
      · exact (ih hm).trans (by simp)
  simp only [BitEncoding.list, List.length_append, BitEncoding.frame_length, BitEncoding.frames_length,
    List.map_map, Function.comp_def, List.length_map]
  omega

/-- The product height theorem only needs bounds on elements actually in the list. -/
theorem product_bounded_mem (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (xs : List K) (H : ℕ) (hH : 1 ≤ H)
    (ha : ∀ x ∈ xs, (certificate basis x).Bounded H H) :
    (Certificate.product data id (certificate basis) xs).Bounded
      ((Certificate.heightConstant data * H) ^ (xs.length + 1))
      ((Certificate.heightConstant data * H) ^ (xs.length + 1)) := by
  induction xs with
  | nil =>
    simpa only [Certificate.product, List.length_nil, Nat.zero_add, pow_one] using
      Certificate.bounded_mono _ (Certificate.one_bounded data) (Nat.le_mul_of_pos_right _ hH)
        (Nat.le_mul_of_pos_right _ hH)
  | cons x xs ih =>
    have hi := ih (fun y hy => ha y (List.mem_cons_of_mem _ hy))
    simpa only [Certificate.product, List.length_cons, pow_succ'] using
      Certificate.bounded_mul_uniform data (certificate basis x)
        (Certificate.product data id (certificate basis) xs) (ha x List.mem_cons_self) hi

/-- The analogous sum bound keeps a single explicitly computed denominator. -/
theorem sum_bounded_mem (xs : List K) (H : ℕ) (hH : 1 ≤ H)
    (ha : ∀ x ∈ xs, (certificate basis x).Bounded H H) :
    (Certificate.sum id (certificate basis) xs).Bounded ((2 * H) ^ (xs.length + 1))
      ((2 * H) ^ (xs.length + 1)) := by
  induction xs with
  | nil =>
    refine ⟨?_, fun i => Nat.zero_le _⟩
    simp only [Certificate.sum, Certificate.zero, List.length_nil, Nat.zero_add, pow_one]
    omega
  | cons x xs ih =>
    have hi := ih (fun y hy => ha y (List.mem_cons_of_mem _ hy))
    have h := Certificate.bounded_add (certificate basis x)
      (Certificate.sum id (certificate basis) xs) (ha x List.mem_cons_self) hi
    apply Certificate.bounded_mono _ h
    · change H * (2 * H) ^ (xs.length + 1) + (2 * H) ^ (xs.length + 1) * H ≤
        (2 * H) ^ (xs.length + 1 + 1)
      rw [pow_succ' (2 * H) (xs.length + 1)]
      nlinarith
    · change H * (2 * H) ^ (xs.length + 1) ≤ (2 * H) ^ (xs.length + 1 + 1)
      calc
        H * (2 * H) ^ (xs.length + 1) ≤ (2 * H) * (2 * H) ^ (xs.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' (2 * H) (xs.length + 1)).symm

/-- Fixed structure constants and coordinate dimension fit into one fixed exponential base. -/
def heightBase (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) : ℕ :=
  max 2 (max (Certificate.heightConstant data) (2 ^ (dimension + 1)))

theorem heightBase_pos (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) :
    0 < heightBase data := lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)

/-- An exponential product over a linearly bounded number of inputs has quadratic exponent. -/
theorem height_power_bound {B c N l : ℕ} (hB : 0 < B) (hc : c ≤ B) (hl : l ≤ N + 1) :
    (c * B ^ N) ^ (l + 1) ≤ B ^ ((N + 2) ^ 2) := by
  calc
    (c * B ^ N) ^ (l + 1) ≤ (B * B ^ N) ^ (l + 1) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) _
    _ = B ^ ((N + 1) * (l + 1)) := by rw [← pow_succ', ← pow_mul]
    _ ≤ B ^ ((N + 2) ^ 2) := Nat.pow_le_pow_right hB (by nlinarith)

/-- Direct polynomial bound for both product and sum of a list with materialized members. -/
theorem list_values_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (xs : List K) (N : ℕ) (hlen : xs.length ≤ N + 1)
    (hcode : ∀ x ∈ xs, ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).encode xs.prod).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension (heightBase data) (heightBase data)).eval ((N+2)^2) ∧
    ((numberFieldEncoding basis).encode xs.sum).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension (heightBase data) (heightBase data)).eval ((N+2)^2) := by
  let B := heightBase data
  have hB : 0 < B := heightBase_pos data
  have hC : 2 ^ (dimension + 1) ≤ B := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have ha : ∀ x ∈ xs, (certificate basis x).Bounded (B ^ N) (B ^ N) := by
    intro x hx
    exact Certificate.bounded_mono _ (certificate_bounded_by_input basis x N (hcode x hx))
      (Nat.pow_le_pow_left hC _) (Nat.pow_le_pow_left hC _)
  have hp := product_bounded_mem data xs (B ^ N) (Nat.one_le_pow _ _ hB) ha
  have hs := sum_bounded_mem xs (B ^ N) (Nat.one_le_pow _ _ hB) ha
  have hpc := height_power_bound hB (show Certificate.heightConstant data ≤ B from
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) hlen
  have hsc := height_power_bound hB (show 2 ≤ B from Nat.le_max_left _ _) hlen
  have hprod := Certificate.encoding_length_le _ (Certificate.bounded_mono _ hp hpc hpc)
  have hsum := Certificate.encoding_length_le _ (Certificate.bounded_mono _ hs hsc hsc)
  simpa only [List.map_id] using And.intro hprod hsum

/-- A single polynomial controls every prefix sum and product of arbitrary materialized inputs. -/
theorem exists_polynomial_prefix_encoding_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ (a : K) (xs : List K) (i : ℕ),
      ((numberFieldEncoding basis).encode (a * (xs.take i).prod)).length ≤
        p.eval (((numberFieldEncoding basis).prod (numberFieldEncoding basis).list).encode (a, xs)).length ∧
      ((numberFieldEncoding basis).encode (a + (xs.take i).sum)).length ≤
        p.eval (((numberFieldEncoding basis).prod (numberFieldEncoding basis).list).encode (a, xs)).length := by
  obtain ⟨data⟩ := exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let p := (EncodingSizeBounds.coordinateOutputPolynomial dimension (heightBase data) (heightBase data)).comp
    ((Polynomial.X + Polynomial.C 2) ^ 2)
  refine ⟨p, fun a xs i => ?_⟩
  let e := numberFieldEncoding basis
  let N := ((e.prod e.list).encode (a, xs)).length
  have hN : N = 2 * (e.encode a).length + (e.list.encode xs).length + 1 :=
    BitEncoding.prod_length e e.list (a, xs)
  have ha : (e.encode a).length ≤ N := by omega
  have hs : (e.list.encode xs).length ≤ N := by omega
  have hlen : (a :: xs.take i).length ≤ N + 1 := by
    have ht : (xs.take i).length ≤ xs.length := by simp
    have hx := (e.list_length_le xs).trans hs
    simp only [List.length_cons]
    omega
  have hcode : ∀ y ∈ a :: xs.take i, (e.encode y).length ≤ N := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha
    · exact (element_length_le_list e xs (List.mem_of_mem_take hy)).trans hs
  have h := list_values_encoding_bound data (a :: xs.take i) N hlen hcode
  simpa only [p, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, List.prod_cons, List.sum_cons] using h

end PlanarHom.MaterializedFieldHeights

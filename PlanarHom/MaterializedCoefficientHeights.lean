import PlanarHom.MaterializedFieldHeights
import PlanarHom.LagrangeCoefficientMachines

/-! Polynomial coefficient-list heights for arbitrary materialized field nodes.
The Boolean expansion below is used only for a shared-denominator certificate;
the machine continues to update coefficients by multiplying one linear factor. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.MaterializedCoefficientHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights
open PolynomialChoiceExpansion LagrangeCoefficientMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

/-- Both choices in one linear factor have exactly the same denominator. -/
def factorCertificate (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (b : Bool) :
    Certificate basis (if b then 1 else -x) where
  denominator := data.denominator * a.denominator
  denominator_pos := Nat.mul_pos data.denominator_pos a.denominator_pos
  numerator := fun i => if b then data.initial i * a.denominator
    else -a.numerator i * data.denominator
  spec := by
    intro i
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Nat.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_neg, map_neg, Pi.neg_apply]
    · rw [← a.spec i]; ring
    · rw [← data.initial_spec i]; ring

theorem factorCertificate_bounded
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (b : Bool) {H : ℕ} (ha : a.Bounded H H) :
    (factorCertificate data a b).Bounded (Certificate.heightConstant data * H)
      (Certificate.heightConstant data * H) := by
  have hd := (Certificate.one_bounded data).1
  have hn := (Certificate.one_bounded data).2
  refine ⟨Nat.mul_le_mul hd ha.1, fun i => ?_⟩
  cases b <;> simp only [factorCertificate, Bool.false_eq_true, ↓reduceIte,
    Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
  · exact (Nat.mul_le_mul (ha.2 i) hd).trans_eq (Nat.mul_comm _ _)
  · exact Nat.mul_le_mul (hn i) ha.1

/-- Product denominators depend only on the factor denominators, not their values. -/
theorem product_denominator_congr {J : Type}
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (f g : J → K) (a : ∀ j, Certificate basis (f j)) (b : ∀ j, Certificate basis (g j))
    (h : ∀ j, (a j).denominator = (b j).denominator) (xs : List J) :
    (Certificate.product data f a xs).denominator =
      (Certificate.product data g b xs).denominator := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Certificate.product, Certificate.mul, h, ih]

/-- One product term in the proof-only Boolean expansion. -/
def choiceCertificate (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (b : Fin n → Bool) :
    Certificate basis (choiceWeight nodes b) := by
  let a := Certificate.product data (fun i => if b i then 1 else -nodes i)
    (fun i => factorCertificate data (certificate basis (nodes i)) (b i)) (List.ofFn id)
  exact {
    denominator := a.denominator
    denominator_pos := a.denominator_pos
    numerator := a.numerator
    spec := by intro i; simpa [a, List.map_ofFn, List.prod_ofFn, choiceWeight] using a.spec i }

theorem choiceCertificate_denominator
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (b : Fin n → Bool) :
    (choiceCertificate data nodes b).denominator =
      (choiceCertificate data nodes (fun _ => false)).denominator :=
  product_denominator_congr data
    (fun i => if b i then 1 else -nodes i) (fun i => if false then 1 else -nodes i)
    (fun i => factorCertificate data (certificate basis (nodes i)) (b i))
    (fun i => factorCertificate data (certificate basis (nodes i)) false) (fun _ => rfl) _

theorem choiceCertificate_bounded
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (b : Fin n → Bool) {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i, (certificate basis (nodes i)).Bounded H H) :
    (choiceCertificate data nodes b).Bounded
      ((Certificate.heightConstant data * (Certificate.heightConstant data * H)) ^ (n + 1))
      ((Certificate.heightConstant data * (Certificate.heightConstant data * H)) ^ (n + 1)) := by
  have hC : 1 ≤ Certificate.heightConstant data := Nat.le_max_left _ _
  have hp := Certificate.product_bounded data (fun i => if b i then 1 else -nodes i)
    (fun i => factorCertificate data (certificate basis (nodes i)) (b i)) (List.ofFn id)
    (by nlinarith : 1 ≤ Certificate.heightConstant data * H) (fun i => factorCertificate_bounded data _ _ (ha i))
  simpa only [List.length_ofFn] using hp

/-- Sum all selected product numerators once, preserving their shared denominator. -/
def coefficientCertificate (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (k : ℕ) :
    Certificate basis ((∏ i, (Polynomial.X - Polynomial.C (nodes i))).coeff k) where
  denominator := (choiceCertificate data nodes (fun _ => false)).denominator
  denominator_pos := (choiceCertificate data nodes (fun _ => false)).denominator_pos
  numerator := fun i => ∑ b : Fin n → Bool,
    if choiceDegree b = k then (choiceCertificate data nodes b).numerator i else 0
  spec := by
    intro i
    rw [linear_product_coefficient]
    simp only [map_sum, Finset.sum_apply, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with hb
    · rw [← choiceCertificate_denominator data nodes b]
      exact (choiceCertificate data nodes b).spec i
    · simp

theorem coefficientCertificate_bounded
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (k : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i, (certificate basis (nodes i)).Bounded H H) :
    (coefficientCertificate data nodes k).Bounded
      (2 ^ n * (Certificate.heightConstant data * (Certificate.heightConstant data * H)) ^ (n + 1))
      ((Certificate.heightConstant data * (Certificate.heightConstant data * H)) ^ (n + 1)) := by
  refine ⟨(choiceCertificate_bounded data nodes _ hH ha).1, fun i => ?_⟩
  apply (natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin n → Bool,
        (Certificate.heightConstant data * (Certificate.heightConstant data * H)) ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · exact (choiceCertificate_bounded data nodes b hH ha).2 i
      · simp
    _ = _ := by simp

/-- Polynomial exponent for a bounded number of materialized linear factors. -/
theorem expansion_height_bound {B C N n : ℕ} (hB : 2 ≤ B) (hC : C ≤ B) (hn : n ≤ N) :
    2 ^ n * (C * (C * B ^ N)) ^ (n + 1) ≤ B ^ ((N + 2) ^ 2) := by
  have hpos : 0 < B := by omega
  have hbase : C * (C * B ^ N) ≤ B ^ (N + 2) := by
    calc
      _ ≤ B * (B * B ^ N) := Nat.mul_le_mul hC (Nat.mul_le_mul_right _ hC)
      _ = _ := by simp only [pow_succ']
  calc
    _ ≤ B ^ n * (B ^ (N + 2)) ^ (n + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hB _) (Nat.pow_le_pow_left hbase _)
    _ = B ^ (n + (N + 2) * (n + 1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hpos (by nlinarith)

/-- Canonical input bits bound every coefficient, independently of any source alphabet. -/
theorem coefficient_encoding_bound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (nodes : Fin n → K) (N : ℕ) (hn : n ≤ N)
    (hcode : ∀ i, ((numberFieldEncoding basis).encode (nodes i)).length ≤ N) (k : ℕ) :
    ((numberFieldEncoding basis).encode
      ((∏ i, (Polynomial.X - Polynomial.C (nodes i))).coeff k)).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension
        (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).eval ((N + 2) ^ 2) := by
  let B := MaterializedFieldHeights.heightBase data
  have hB : 2 ≤ B := Nat.le_max_left _ _
  have hpos : 0 < B := by omega
  have hC : Certificate.heightConstant data ≤ B :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcanonical : 2 ^ (dimension + 1) ≤ B :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have ha : ∀ i, (certificate basis (nodes i)).Bounded (B ^ N) (B ^ N) := by
    intro i
    exact Certificate.bounded_mono _ (certificate_bounded_by_input basis (nodes i) N (hcode i))
      (Nat.pow_le_pow_left hcanonical _) (Nat.pow_le_pow_left hcanonical _)
  have hb := coefficientCertificate_bounded data nodes k (Nat.one_le_pow _ _ hpos) ha
  have hh := expansion_height_bound hB hC hn
  apply Certificate.encoding_length_le (coefficientCertificate data nodes k)
  apply Certificate.bounded_mono _ hb hh
  exact (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)).trans hh

/-- The literal coefficient list has a uniform polynomial encoding bound whenever
all node words and their count are charged to N input bits. -/
theorem exists_polynomial_encoding_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ (nodes : List K) (N : ℕ), nodes.length ≤ N →
      (∀ x ∈ nodes, ((numberFieldEncoding basis).encode x).length ≤ N) →
      ((numberFieldEncoding basis).list.encode (productCoefficients nodes)).length ≤ p.eval N := by
  obtain ⟨data⟩ := exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let q := (EncodingSizeBounds.coordinateOutputPolynomial dimension
    (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).comp
      ((Polynomial.X + Polynomial.C 2) ^ 2)
  let p := (Polynomial.C 2 * q + Polynomial.C 3) * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1
  refine ⟨p, fun nodes N hlen hcode => ?_⟩
  have hpoly : (nodes.map (fun μ => Polynomial.X - Polynomial.C μ)).prod =
      ∏ i : Fin nodes.length, (Polynomial.X - Polynomial.C (nodes.get i)) := by
    conv_lhs => rw [← List.ofFn_get nodes]
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  have hc : ∀ x ∈ productCoefficients nodes, ((numberFieldEncoding basis).encode x).length ≤ q.eval N := by
    intro x hx
    rw [productCoefficients_ofFn, hpoly] at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hb := coefficient_encoding_bound data (fun i => nodes.get i) N hlen
      (fun i => hcode _ (List.get_mem nodes i)) i.val
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using hb
  have hb := CoefficientListHeights.list_encoding_length_le (numberFieldEncoding basis) _ (q.eval N) hc
  rw [productCoefficients_length] at hb
  apply hb.trans
  have hm := Nat.mul_le_mul_left (2 * q.eval N + 3) (Nat.add_le_add_right hlen 1)
  simpa only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using
    Nat.add_le_add_right hm 1

/-- Exact node-list serialization alone pays for the complete coefficient vector. -/
theorem exists_product_length_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ nodes : List K,
      ((numberFieldEncoding basis).list.encode (productCoefficients nodes)).length ≤
        p.eval ((numberFieldEncoding basis).list.encode nodes).length := by
  obtain ⟨p, hp⟩ := exists_polynomial_encoding_bound basis
  exact ⟨p, fun nodes => hp nodes _ ((numberFieldEncoding basis).list_length_le nodes)
    (fun _ hx => MaterializedFieldHeights.element_length_le_list _ nodes hx)⟩

end PlanarHom.MaterializedCoefficientHeights

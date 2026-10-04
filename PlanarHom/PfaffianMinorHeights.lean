import PlanarHom.MaterializedCoefficientHeights
import PlanarHom.UniformFieldArithmeticHeights

/-!
# Genuine determinant-minor height certificates

Every certificate below represents the indicated determinant of the actual input
matrix. All Leibniz terms have one shared denominator; no factorial-size
iteration of rational additions is used in the height proof. This is an algebraic
size bound, independent of any proposed elimination correctness invariant.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PfaffianMinorHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

/-- Put a finite family of certificates over its literal product denominator. -/
def commonCertificate {J : Type} [Fintype J] [DecidableEq J]
    (f : J → K) (a : ∀ j, Certificate basis (f j)) (j : J) : Certificate basis (f j) where
  denominator := ∏ t, (a t).denominator
  denominator_pos := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun t _ => (a t).denominator_pos.ne'))
  numerator := fun i => (a j).numerator i * ((∏ t ∈ Finset.univ.erase j, (a t).denominator : ℕ) : ℤ)
  spec := by
    intro i
    rw [← Finset.prod_erase_mul Finset.univ (fun t => (a t).denominator) (Finset.mem_univ j)]
    simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    rw [← (a j).spec i]
    ring

theorem commonCertificate_bounded {J : Type} [Fintype J] [DecidableEq J]
    (f : J → K) (a : ∀ j, Certificate basis (f j)) {H : ℕ} (hH : 0 < H)
    (ha : ∀ j, (a j).Bounded H H) (j : J) :
    (commonCertificate f a j).Bounded (H ^ (Fintype.card J + 1)) (H ^ (Fintype.card J + 1)) := by
  have hp (s : Finset J) : (∏ t ∈ s, (a t).denominator) ≤ H ^ s.card := by
    simpa using Finset.prod_le_prod' (s := s) (fun t _ => (ha t).1)
  refine ⟨?_, fun i => ?_⟩
  · exact (hp Finset.univ).trans (Nat.pow_le_pow_right hH (by simp))
  · simp only [commonCertificate, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      _ ≤ H * H ^ (Finset.univ.erase j).card := Nat.mul_le_mul (ha j |>.2 i) (hp _)
      _ ≤ H * H ^ Fintype.card J := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hH
        (by simpa using (Finset.card_erase_le (s := Finset.univ) (a := j))))
      _ = _ := (pow_succ' _ _).symm

/-- Integer signs do not change a common denominator. -/
def signedCertificate {x : K} (a : Certificate basis x) (z : ℤ) :
    Certificate basis (z • x) where
  denominator := a.denominator
  denominator_pos := a.denominator_pos
  numerator := fun i => z * a.numerator i
  spec := by
    intro i
    change (a.denominator : ℚ) * (basis.equivFun (z • x)) i = _
    rw [map_zsmul]
    simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, ← a.spec i]
    ring

theorem signedCertificate_bounded {x : K} (a : Certificate basis x) (z : ℤˣ)
    {N D : ℕ} (ha : a.Bounded N D) : (signedCertificate a (z : ℤ)).Bounded N D := by
  refine ⟨ha.1, fun i => ?_⟩
  simpa only [signedCertificate, Int.natAbs_mul, Int.units_natAbs, one_mul] using ha.2 i

/-- Certificate for a matrix entry, sharing all entry denominators. -/
def entryCertificate {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    Certificate basis (A i j) :=
  commonCertificate (fun p : Fin n × Fin n => A p.1 p.2)
    (fun p => certificate basis (A p.1 p.2)) (i, j)

/-- The unsigned product in one determinant monomial. -/
def monomialCertificate
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (σ : Equiv.Perm (Fin n)) :
    Certificate basis (∏ i, A (σ i) i) := by
  let a := Certificate.product data (fun i => A (σ i) i)
    (fun i => entryCertificate A (σ i) i) (List.ofFn id)
  exact {
    denominator := a.denominator
    denominator_pos := a.denominator_pos
    numerator := a.numerator
    spec := by intro i; simpa [a, List.map_ofFn, List.prod_ofFn] using a.spec i }

theorem monomialCertificate_denominator
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (σ : Equiv.Perm (Fin n)) :
    (monomialCertificate data A σ).denominator =
      (monomialCertificate data A (Equiv.refl _)).denominator :=
  MaterializedCoefficientHeights.product_denominator_congr data
    (fun i => A (σ i) i) (fun i => A i i)
    (fun i => entryCertificate A (σ i) i) (fun i => entryCertificate A i i) (fun _ => rfl) _

theorem monomialCertificate_bounded
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (σ : Equiv.Perm (Fin n)) {H : ℕ}
    (hH : 0 < H) (ha : ∀ i j, (certificate basis (A i j)).Bounded H H) :
    (monomialCertificate data A σ).Bounded
      ((Certificate.heightConstant data * H ^ (n*n+1)) ^ (n+1))
      ((Certificate.heightConstant data * H ^ (n*n+1)) ^ (n+1)) := by
  have he (i j : Fin n) : (entryCertificate (basis := basis) A i j).Bounded (H ^ (n*n+1)) (H ^ (n*n+1)) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      commonCertificate_bounded (fun p : Fin n × Fin n => A p.1 p.2)
        (fun p => certificate basis (A p.1 p.2)) hH (fun p => ha p.1 p.2) (i,j)
  have hp := Certificate.product_bounded data (fun i => A (σ i) i)
    (fun i => entryCertificate A (σ i) i) (List.ofFn id)
    (Nat.one_le_pow _ _ hH) (fun i => he (σ i) i)
  simpa only [List.length_ofFn] using hp

/-- Sum the signed integer numerators once, preserving their common denominator. -/
def determinantCertificate
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Certificate basis A.det where
  denominator := (monomialCertificate data A (Equiv.refl _)).denominator
  denominator_pos := (monomialCertificate data A (Equiv.refl _)).denominator_pos
  numerator := fun i => ∑ σ : Equiv.Perm (Fin n),
    (Equiv.Perm.sign σ : ℤ) * (monomialCertificate data A σ).numerator i
  spec := by
    intro i
    rw [Matrix.det_apply]
    simp only [map_sum, Finset.sum_apply, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← monomialCertificate_denominator data A σ]
    exact (signedCertificate (monomialCertificate data A σ) (Equiv.Perm.sign σ : ℤ)).spec i

theorem determinantCertificate_bounded
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {H : ℕ}
    (hH : 0 < H) (ha : ∀ i j, (certificate basis (A i j)).Bounded H H) :
    (determinantCertificate data A).Bounded
      (n.factorial * (Certificate.heightConstant data * H ^ (n*n+1)) ^ (n+1))
      ((Certificate.heightConstant data * H ^ (n*n+1)) ^ (n+1)) := by
  refine ⟨(monomialCertificate_bounded data A (Equiv.refl _) hH ha).1, fun i => ?_⟩
  apply (natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin n),
        (Certificate.heightConstant data * H ^ (n*n+1)) ^ (n+1) := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Int.natAbs_mul, Int.units_natAbs, one_mul] using
        (monomialCertificate_bounded data A σ hH ha).2 i
    _ = _ := by simp [Fintype.card_perm]

/-- The factorial number of terms costs only a quadratic exponent. -/
theorem factorial_le_base_square {B N n : ℕ} (hB : 2 ≤ B) (hn : n ≤ N) :
    n.factorial ≤ B ^ (N*N) := by
  have hnB : n ≤ B ^ N := (Nat.lt_two_pow_self (n := n)).le.trans
    ((Nat.pow_le_pow_left hB n).trans (Nat.pow_le_pow_right (by omega) hn))
  calc
    _ ≤ n^n := Nat.factorial_le_pow n
    _ ≤ (B^N)^n := Nat.pow_le_pow_left hnB n
    _ = B^(N*n) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left N hn)

/-- A shared-denominator determinant bound has a polynomial exponent. -/
theorem determinant_height_exponent {B C N n : ℕ} (hB : 2 ≤ B) (hC : C ≤ B) (hn : n ≤ N) :
    n.factorial * (C * (B^N)^(n*n+1))^(n+1) ≤ B^((N+2)^4) := by
  have hb : C * (B^N)^(n*n+1) ≤ B^(1+N*(N*N+1)) := by
    calc
      _ ≤ B * (B^N)^(N*N+1) := Nat.mul_le_mul hC
        (Nat.pow_le_pow_right (pow_pos (by omega) _) (by nlinarith))
      _ = _ := by rw [← pow_mul, pow_add, pow_one]
  calc
    _ ≤ B^(N*N) * (B^(1+N*(N*N+1)))^(N+1) := Nat.mul_le_mul
      (factorial_le_base_square hB hn)
      ((Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (pow_pos (by omega) _) (by omega)))
    _ = B^(N*N+(1+N*(N*N+1))*(N+1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.zero_le (N^3)])

/-- Determinants of arbitrarily selected input entries have polynomial canonical size. -/
theorem determinant_encoding_bound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (N : ℕ) (hn : n ≤ N)
    (hcode : ∀ i j, ((numberFieldEncoding basis).encode (A i j)).length ≤ N) :
    ((numberFieldEncoding basis).encode A.det).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension
        (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).eval ((N+2)^4) := by
  let B := MaterializedFieldHeights.heightBase data
  have hB : 2 ≤ B := Nat.le_max_left _ _
  have hC : Certificate.heightConstant data ≤ B :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcanonical : 2 ^ (dimension+1) ≤ B :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have ha : ∀ i j, (certificate basis (A i j)).Bounded (B^N) (B^N) := by
    intro i j
    exact Certificate.bounded_mono _ (certificate_bounded_by_input basis (A i j) N (hcode i j))
      (Nat.pow_le_pow_left hcanonical _) (Nat.pow_le_pow_left hcanonical _)
  have hb := determinantCertificate_bounded data A (pow_pos (by omega) _) ha
  have he := determinant_height_exponent hB hC hn
  apply Certificate.encoding_length_le (determinantCertificate data A)
  apply Certificate.bounded_mono _ hb he
  exact (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)).trans he

/-- The exact nested-list input representation used by the elimination machine. -/
def matrixInputLength (basis : Module.Basis (Fin dimension) ℚ K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ :=
  ((numberFieldEncoding basis).list.list.encode (List.ofFn (fun i => List.ofFn (A i)))).length

theorem dimension_le_matrixInputLength (basis : Module.Basis (Fin dimension) ℚ K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : n ≤ matrixInputLength basis A := by
  simpa only [List.length_ofFn] using (numberFieldEncoding basis).list.list_length_le
    (List.ofFn (fun i => List.ofFn (A i)))

theorem entry_length_le_matrixInputLength (basis : Module.Basis (Fin dimension) ℚ K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ((numberFieldEncoding basis).encode (A i j)).length ≤ matrixInputLength basis A :=
  (MaterializedFieldHeights.element_length_le_list _ (List.ofFn (A i))
    (List.mem_ofFn.mpr ⟨j,rfl⟩)).trans
      (MaterializedFieldHeights.element_length_le_list _ (List.ofFn (fun i => List.ofFn (A i)))
        (List.mem_ofFn.mpr ⟨i,rfl⟩))

/-- A single polynomial bounds every actual input minor, including empty minors. -/
theorem exists_polynomial_minor_encoding_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
      (rows cols : Fin m → Fin n), m ≤ n →
      ((numberFieldEncoding basis).encode (A.submatrix rows cols).det).length ≤
        p.eval (matrixInputLength basis A) := by
  obtain ⟨data⟩ := exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let p := (EncodingSizeBounds.coordinateOutputPolynomial dimension
    (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).comp
      ((Polynomial.X+Polynomial.C 2)^4)
  refine ⟨p, fun A rows cols hm => ?_⟩
  simpa only [p, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] using
    determinant_encoding_bound data (A.submatrix rows cols) (matrixInputLength basis A)
      (hm.trans (dimension_le_matrixInputLength basis A))
      (fun i j => entry_length_le_matrixInputLength basis A (rows i) (cols j))

/-- Ratios of genuine input minors have polynomial canonical bit length. No
nonvanishing or correctness hypothesis is needed for this total-field bound. -/
theorem exists_polynomial_minor_ratio_encoding_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ {n m l : ℕ} (A : Matrix (Fin n) (Fin n) K)
      (rows cols : Fin m → Fin n) (rows' cols' : Fin l → Fin n), m ≤ n → l ≤ n →
      ((numberFieldEncoding basis).encode
        ((A.submatrix rows cols).det / (A.submatrix rows' cols').det)).length ≤
        p.eval (matrixInputLength basis A) := by
  obtain ⟨q, hq⟩ := exists_polynomial_minor_encoding_bound basis
  obtain ⟨data⟩ := exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let H := Certificate.heightConstant data
  let p := (UniformFieldHeights.operationPolynomial dimension).comp (q + Polynomial.C H)
  refine ⟨p, fun A rows cols rows' cols' hm hl => ?_⟩
  have hdata : Certificate.heightConstant data ≤ 2^H := (Nat.lt_two_pow_self (n := H)).le
  have hb := UniformFieldHeights.operations_encoding_bound data (le_refl dimension) hdata
    (A.submatrix rows cols).det (A.submatrix rows' cols').det (q.eval (matrixInputLength basis A))
    (hq A rows cols hm) (hq A rows' cols' hl)
  simpa only [p, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C] using hb.2.2.2

/-- Bordered minors may have one more index than the ambient matrix (with repeated
indices). Their degree is still polynomially bounded by the actual input. -/
theorem exists_polynomial_bordered_ratio_encoding_bound (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ p : Polynomial ℕ, ∀ {n : ℕ} {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (A : Matrix (Fin n) (Fin n) K) (rows cols : I → Fin n) (rows' cols' : J → Fin n),
      Fintype.card I ≤ n+1 → Fintype.card J ≤ n+1 →
      ((numberFieldEncoding basis).encode
        ((A.submatrix rows cols).det / (A.submatrix rows' cols').det)).length ≤
        p.eval (matrixInputLength basis A) := by
  obtain ⟨data⟩ := exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let q := (EncodingSizeBounds.coordinateOutputPolynomial dimension
    (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).comp
      ((Polynomial.X+Polynomial.C 3)^4)
  let H := Certificate.heightConstant data
  let p := (UniformFieldHeights.operationPolynomial dimension).comp (q + Polynomial.C H)
  refine ⟨p, ?_⟩
  intro n I J _ _ _ _ A rows cols rows' cols' hm hl
  have hminor {I : Type} [Fintype I] [DecidableEq I] (r c : I → Fin n) (hI : Fintype.card I ≤ n+1) :
      ((numberFieldEncoding basis).encode (A.submatrix r c).det).length ≤ q.eval (matrixInputLength basis A) := by
    let e := (Fintype.equivFin I).symm
    have hd : (A.submatrix r c).det = (A.submatrix (r ∘ e) (c ∘ e)).det :=
      (Matrix.det_submatrix_equiv_self e (A.submatrix r c)).symm
    rw [hd]
    have hh := determinant_encoding_bound data (A.submatrix (r ∘ e) (c ∘ e))
      (matrixInputLength basis A+1)
      (hI.trans (Nat.add_le_add_right (dimension_le_matrixInputLength basis A) 1))
      (fun i j => (entry_length_le_matrixInputLength basis A (r (e i)) (c (e j))).trans (by omega))
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Nat.add_assoc] using hh
  have hdata : Certificate.heightConstant data ≤ 2^H := (Nat.lt_two_pow_self (n := H)).le
  have hb := UniformFieldHeights.operations_encoding_bound data (le_refl dimension) hdata
    (A.submatrix rows cols).det (A.submatrix rows' cols').det (q.eval (matrixInputLength basis A))
    (hminor rows cols hm) (hminor rows' cols' hl)
  simpa only [p, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C] using hb.2.2.2

end PlanarHom.PfaffianMinorHeights

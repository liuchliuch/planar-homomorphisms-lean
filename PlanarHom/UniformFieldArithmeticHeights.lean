import PlanarHom.UniformFieldHeights

/-! Basis-independent exact-field arithmetic heights, including total inversion. -/
noncomputable section
namespace PlanarHom.UniformFieldHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights EncodingSizeBounds
open MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

theorem canonical_bounded {c : ℕ} (hd : dimension ≤ c) (x : K) (N : ℕ)
    (hx : ((numberFieldEncoding basis).encode x).length ≤ N) :
    (certificate basis x).Bounded (2 ^ ((c+1)*N)) (2 ^ ((c+1)*N)) := by
  have hpow : (2 ^ (dimension+1)) ^ N ≤ 2 ^ ((c+1)*N) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))
  exact Certificate.bounded_mono _ (certificate_bounded_by_input basis x N hx) hpow hpow

theorem encoding_length_uniform {c E : ℕ} (hd : dimension ≤ c) {x : K}
    (a : Certificate basis x) (ha : a.Bounded (2^E) (2^E)) :
    ((numberFieldEncoding basis).encode x).length ≤ (coordinateOutputPolynomial c 2 2).eval E :=
  (Certificate.encoding_length_le a ha).trans (coordinatePolynomial_dimension_mono hd)

def inverseExponentConstant (c : ℕ) : ℕ := c.factorial + (c+2)^2 + 2

def inversePolynomial (c : ℕ) : Polynomial ℕ :=
  (coordinateOutputPolynomial c 2 2).comp
    (Polynomial.C (inverseExponentConstant c) * (Polynomial.X+1))

theorem inputExponent_le {c N H : ℕ} :
    (c+1)*N ≤ inverseExponentConstant c * (N+H+1) := by
  have hc : c+1 ≤ inverseExponentConstant c := by dsimp [inverseExponentConstant]; nlinarith
  exact Nat.mul_le_mul hc (show N ≤ N+H+1 from by omega)

theorem inverseHeight_le (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H N : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H) :
    Certificate.inverseHeightBound data (2^((c+1)*N)) (2^((c+1)*N)) ≤
      2 ^ (inverseExponentConstant c * (N+H+1)) := by
  have hg : growthConstant data ≤ 2^H := (show growthConstant data ≤ Certificate.heightConstant data from
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))).trans hdata
  have hf : dimension.factorial ≤ 2 ^ c.factorial :=
    (Nat.factorial_le hd).trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := c.factorial)))
  have hs : growthConstant data * (2^((c+1)*N) + 2^((c+1)*N)) ≤ 2^(H+(c+1)*N+1) := by
    calc
      _ ≤ 2^H * (2^((c+1)*N) + 2^((c+1)*N)) := Nat.mul_le_mul_right _ hg
      _ = _ := by rw [pow_succ, pow_add]; ring
  have hp : (growthConstant data * (2^((c+1)*N) + 2^((c+1)*N)))^dimension ≤
      2^((H+(c+1)*N+1)*c) := by
    calc
      _ ≤ (2^(H+(c+1)*N+1))^dimension := Nat.pow_le_pow_left hs _
      _ = 2^((H+(c+1)*N+1)*dimension) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hd)
  have hex : c.factorial + (H+(c+1)*N+1)*c ≤ inverseExponentConstant c * (N+H+1) := by
    have hinner : H+(c+1)*N+1 ≤ (c+2)*(N+H+1) := by nlinarith
    have hm := Nat.mul_le_mul_right c hinner
    have hc : c.factorial + (c+2)*c ≤ inverseExponentConstant c := by dsimp [inverseExponentConstant]; nlinarith
    calc
      _ ≤ c.factorial * (N+H+1) + ((c+2)*(N+H+1))*c := by nlinarith
      _ = (c.factorial+(c+2)*c)*(N+H+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  calc
    _ ≤ 2^c.factorial * 2^((H+(c+1)*N+1)*c) := Nat.mul_le_mul hf hp
    _ = 2^(c.factorial+(H+(c+1)*N+1)*c) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hex

/-- Total inverse and negation have one uniform polynomial bound, including x=0. -/
theorem inverse_neg_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (x : K) (N : ℕ) (hx : ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).encode x⁻¹).length ≤ (inversePolynomial c).eval (N+H) ∧
    ((numberFieldEncoding basis).encode (-x)).length ≤ (inversePolynomial c).eval (N+H) := by
  have ha := canonical_bounded hd x N hx
  have hp : 2^((c+1)*N) ≤ 2^(inverseExponentConstant c*(N+H+1)) :=
    Nat.pow_le_pow_right (by omega) inputExponent_le
  have hn := encoding_length_uniform hd (certificate basis x).neg
    (Certificate.bounded_mono _ (Certificate.bounded_neg _ ha) hp hp)
  have hi : ((numberFieldEncoding basis).encode x⁻¹).length ≤
      (coordinateOutputPolynomial c 2 2).eval (inverseExponentConstant c*(N+H+1)) := by
    by_cases hz : x = 0
    · subst x
      rw [inv_zero]
      exact encoding_length_uniform hd Certificate.zero
        ⟨Nat.one_le_pow _ _ (by omega), fun _ => Nat.zero_le _⟩
    · have hb := Certificate.bounded_inv data (certificate basis x) hz ha
      have hh := inverseHeight_le data (N := N) hd hdata
      exact encoding_length_uniform hd ((certificate basis x).inv data hz) (Certificate.bounded_mono _ hb hh hh)
  simpa only [inversePolynomial, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using And.intro hi hn

/-- A common polynomial for all four arithmetic operations and the original word size. -/
def operationPolynomial (c : ℕ) : Polynomial ℕ :=
  Polynomial.X + inversePolynomial c + (valuePolynomial c).comp (Polynomial.X + inversePolynomial c + 2)

theorem operationPolynomial_ge (c T : ℕ) : T ≤ (operationPolynomial c).eval T ∧
    (inversePolynomial c).eval T ≤ (operationPolynomial c).eval T := by
  simp only [operationPolynomial, Polynomial.eval_add, Polynomial.eval_X]
  omega

/-- Addition, subtraction, multiplication, and division all retain polynomial
canonical size uniformly over every basis satisfying the displayed explicit budget. -/
theorem operations_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (x y : K) (N : ℕ) (hx : ((numberFieldEncoding basis).encode x).length ≤ N)
    (hy : ((numberFieldEncoding basis).encode y).length ≤ N) :
    ((numberFieldEncoding basis).encode (x+y)).length ≤ (operationPolynomial c).eval (N+H) ∧
    ((numberFieldEncoding basis).encode (x-y)).length ≤ (operationPolynomial c).eval (N+H) ∧
    ((numberFieldEncoding basis).encode (x*y)).length ≤ (operationPolynomial c).eval (N+H) ∧
    ((numberFieldEncoding basis).encode (x/y)).length ≤ (operationPolynomial c).eval (N+H) := by
  let Q := (inversePolynomial c).eval (N+H)
  let L := N+Q+1
  have hi := inverse_neg_encoding_bound data hd hdata y N hy
  have hbounds (z : K) (hz : ((numberFieldEncoding basis).encode z).length ≤ N+Q) :
      ((numberFieldEncoding basis).encode (x*z)).length ≤ (operationPolynomial c).eval (N+H) ∧
      ((numberFieldEncoding basis).encode (x+z)).length ≤ (operationPolynomial c).eval (N+H) := by
    have hl : ([x,z] : List K).length ≤ L+1 := by simp; dsimp [L]; omega
    have hcode : ∀ a ∈ [x,z], ((numberFieldEncoding basis).encode a).length ≤ L := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx.trans (by dsimp [L]; omega)
      · have he : a = z := List.mem_singleton.mp ha
        subst a
        exact hz.trans (by dsimp [L]; omega)
    have hb := list_values_encoding_bound data hd hdata [x,z] L hl hcode
    have hp : (valuePolynomial c).eval (L+H) ≤ (operationPolynomial c).eval (N+H) := by
      have he : L+H ≤ (N+H)+Q+2 := by dsimp [L]; omega
      have hm := natPolynomial_monotone (valuePolynomial c) he
      dsimp only at hm
      simp only [operationPolynomial, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_ofNat] at ⊢
      change _ ≤ (N+H)+Q+(valuePolynomial c).eval ((N+H)+Q+2)
      omega
    simpa using And.intro (hb.1.trans hp) (hb.2.trans hp)
  have hy' := hbounds y (hy.trans (by omega))
  have hn' := hbounds (-y) (hi.2.trans (by dsimp [Q]; omega))
  have hi' := hbounds y⁻¹ (hi.1.trans (by dsimp [Q]; omega))
  simpa only [sub_eq_add_neg, div_eq_mul_inv] using ⟨hy'.2, hn'.2, hy'.1, hi'.1⟩

end PlanarHom.UniformFieldHeights

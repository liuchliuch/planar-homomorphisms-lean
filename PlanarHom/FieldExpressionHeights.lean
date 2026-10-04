import PlanarHom.FieldCoordinateHeights

/-! Height certificates for finite arithmetic expressions and fixed alphabets. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.FieldCoordinateCertificates
open IntegerCoordinateBounds

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

namespace Certificate

/-- The zero certificate has unit denominator. -/
def zero : Certificate basis (0 : K) where
  denominator := 1
  denominator_pos := Nat.zero_lt_one
  numerator := fun _ => 0
  spec := by intro i; simp

/-- The unit certificate is supplied by the same fixed clearing data as multiplication. -/
def one (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) :
    Certificate basis (1 : K) where
  denominator := data.denominator
  denominator_pos := data.denominator_pos
  numerator := data.initial
  spec := data.initial_spec

/-- A uniform factor for all fixed multiplication structure constants and unit coordinates. -/
def heightConstant (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) : ℕ :=
  max 1 (max data.denominator (max (growthConstant data) (dimension * growthConstant data)))

theorem one_bounded (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) :
    (one data).Bounded (heightConstant data) (heightConstant data) := by
  refine ⟨(Nat.le_max_left _ _).trans (Nat.le_max_right _ _), fun i => ?_⟩
  exact (initial_le_growth basis data i).trans
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

theorem bounded_mono {x : K} (a : Certificate basis x) {N D N' D' : ℕ}
    (ha : a.Bounded N D) (hN : N ≤ N') (hD : D ≤ D') : a.Bounded N' D' :=
  ⟨ha.1.trans hD, fun i => (ha.2 i).trans hN⟩

theorem bounded_mul_uniform (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x y : K} (a : Certificate basis x) (b : Certificate basis y) {A B : ℕ}
    (ha : a.Bounded A A) (hb : b.Bounded B B) :
    (a.mul data b).Bounded (heightConstant data * A * B) (heightConstant data * A * B) := by
  apply bounded_mono _ (bounded_mul data a b ha hb)
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))

/-- Concrete recursive certificate for a product of field values. -/
def product {J : Type} (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (f : J → K) (a : ∀ j, Certificate basis (f j)) :
    (xs : List J) → Certificate basis ((xs.map f).prod)
  | [] => one data
  | j :: xs => (a j).mul data (product data f a xs)

/-- A polynomial number of bounded-height factors has only polynomially many bits. -/
theorem product_bounded {J : Type}
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (f : J → K) (a : ∀ j, Certificate basis (f j)) (xs : List J) {H : ℕ}
    (hH : 1 ≤ H) (ha : ∀ j, (a j).Bounded H H) :
    (product data f a xs).Bounded ((heightConstant data * H) ^ (xs.length + 1))
      ((heightConstant data * H) ^ (xs.length + 1)) := by
  induction xs with
  | nil =>
    simpa only [product, List.length_nil, Nat.zero_add, pow_one] using
      bounded_mono _ (one_bounded data) (Nat.le_mul_of_pos_right _ hH)
        (Nat.le_mul_of_pos_right _ hH)
  | cons j xs ih =>
    simpa only [product, List.length_cons, pow_succ'] using
      bounded_mul_uniform data (a j) (product data f a xs) (ha j) ih

/-- Concrete recursive certificate for a sum of field values. -/
def sum {J : Type} (f : J → K) (a : ∀ j, Certificate basis (f j)) :
    (xs : List J) → Certificate basis ((xs.map f).sum)
  | [] => zero
  | j :: xs => (a j).add (sum f a xs)

/-- Common denominators for a finite sum can be chosen with controlled exponential height. -/
theorem sum_bounded {J : Type} (f : J → K) (a : ∀ j, Certificate basis (f j))
    (xs : List J) {H : ℕ} (hH : 1 ≤ H) (ha : ∀ j, (a j).Bounded H H) :
    (sum f a xs).Bounded ((2 * H) ^ (xs.length + 1)) ((2 * H) ^ (xs.length + 1)) := by
  induction xs with
  | nil =>
    refine ⟨?_, fun i => Nat.zero_le _⟩
    simp only [sum, zero, List.length_nil, Nat.zero_add, pow_one]
    omega
  | cons j xs ih =>
    have h := bounded_add (a j) (sum f a xs) (ha j) ih
    apply bounded_mono _ h
    · simp only [List.length_cons, pow_succ']
      ring_nf
      omega
    · change H * (2 * H) ^ (xs.length + 1) ≤ (2 * H) ^ (xs.length + 1 + 1)
      calc
        H * (2 * H) ^ (xs.length + 1) ≤ (2 * H) * (2 * H) ^ (xs.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' (2 * H) (xs.length + 1)).symm

end Certificate
end PlanarHom.FieldCoordinateCertificates

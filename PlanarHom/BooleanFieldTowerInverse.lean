import PlanarHom.BooleanFieldTowerAlgebra

/-! Inversion in the fixed squarefree radical algebra uses recursive conjugation
and a single base-field division. It applies to units certified by the norm;
no field structure on the tower is asserted. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerInverse
open BooleanFieldTower BooleanFieldTowerAlgebra
variable {K : Type*} [Field K]

/-- A total base-field algorithm; its inverse specification needs nonzero norm. -/
def inverse (D : ℕ → K) : (n : ℕ) → Tower K n → Tower K n
  | 0,p => p⁻¹
  | n+1,p =>
    let q := inverse D n (sub n (mul D n p.1 p.1)
      (mul D n (embed n (D n)) (mul D n p.2 p.2)))
    (mul D n p.1 q, neg n (mul D n p.2 q))

/-- The recursive formula is an actual multiplicative inverse whenever its
base-field norm is nonzero. This includes square and dependent radicands. -/
theorem mul_inverse (D : ℕ → K) (n : ℕ) (p : Tower K n)
    (h : norm D n p ≠ 0) : mul D n p (inverse D n p) = embed n 1 := by
  induction n with
  | zero => exact mul_inv_cancel₀ h
  | succ n ih =>
    let a : Carrier D n := p.1
    let b : Carrier D n := p.2
    let d : Carrier D n := embed n (D n)
    let q : Carrier D n := inverse D n (sub n (mul D n p.1 p.1)
      (mul D n (embed n (D n)) (mul D n p.2 p.2)))
    have hi : (a*a-d*(b*b))*q=1 := by
      simpa only [mul_eq,sub_eq,one_eq] using ih
        (sub n (mul D n p.1 p.1) (mul D n (embed n (D n)) (mul D n p.2 p.2))) h
    apply Prod.ext
    · change add n (mul D n p.1 (mul D n p.1 q))
        (mul D n (embed n (D n)) (mul D n p.2 (neg n (mul D n p.2 q)))) = embed n 1
      have he : a*(a*q)+d*(b*(-(b*q)))=1 := by
        calc
          _ = (a*a-d*(b*b))*q := by ring
          _ = 1 := hi
      simpa only [add_eq,mul_eq,neg_eq,one_eq] using he
    · change add n (mul D n p.1 (neg n (mul D n p.2 q)))
        (mul D n p.2 (mul D n p.1 q)) = zero n
      have he : a*(-(b*q))+b*(a*q)=0 := by ring
      simpa only [add_eq,mul_eq,neg_eq,zero_eq] using he

theorem inverse_mul (D : ℕ → K) (n : ℕ) (p : Tower K n)
    (h : norm D n p ≠ 0) : mul D n (inverse D n p) p = embed n 1 := by
  have hc := @mul_comm (Carrier D n) inferInstance (inverse D n p) p
  rw [mul_eq,mul_eq] at hc
  exact hc.trans (mul_inverse D n p h)

/-- A certified norm yields a unit of the genuine represented algebra. -/
def unit (D : ℕ → K) (n : ℕ) (p : Tower K n) (h : norm D n p ≠ 0) :
    (Carrier D n)ˣ where
  val := p
  inv := inverse D n p
  val_inv := by simpa only [mul_eq,one_eq] using mul_inverse D n p h
  inv_val := by simpa only [mul_eq,one_eq] using inverse_mul D n p h

theorem isUnit_of_norm_ne_zero (D : ℕ → K) (n : ℕ) (p : Tower K n)
    (h : norm D n p ≠ 0) : @IsUnit (Carrier D n) inferInstance p := ⟨unit D n p h,rfl⟩

/-- The constant squarefree coefficient, extracted without selecting a radical. -/
def constantCoeff : (n : ℕ) → Tower K n → K
  | 0,p => p
  | n+1,p => constantCoeff n p.1

@[simp] theorem constantCoeff_embed (n : ℕ) (c : K) :
    constantCoeff n (embed n c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end PlanarHom.BooleanFieldTowerInverse

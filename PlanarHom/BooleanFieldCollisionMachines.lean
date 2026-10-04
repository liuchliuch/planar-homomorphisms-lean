import PlanarHom.BooleanFieldCollision
import PlanarHom.BooleanFieldTowerMachines
import PlanarHom.QuadraticBinomialPowerMachines

/-! Actual polynomial-bit-cost evaluation of the frozen collision eliminant
inside one fixed number field. All variable powers use the compiled binomial
coefficient algorithm; no radical computation or iteration-height oracle is used. -/
noncomputable section
namespace PlanarHom.BooleanFieldCollisionMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BooleanFieldTower BooleanFieldCollision
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Conjugation in the formal quadratic algebra is valid for every radicand. -/
def conjugate (D : K) : QuadraticAlgebra K D 0 →+* QuadraticAlgebra K D 0 where
  toFun z := ⟨z.re,-z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by ext <;> simp <;> ring
  map_mul' z w := by ext <;> simp <;> ring

omit [Algebra ℚ K] in
@[simp] theorem negative_branch_power (D c : K) (k : ℕ) :
    (⟨c,-1⟩ : QuadraticAlgebra K D 0)^k =
      ⟨((⟨c,1⟩ : QuadraticAlgebra K D 0)^k).re,
        -((⟨c,1⟩ : QuadraticAlgebra K D 0)^k).im⟩ := by
  have h := (conjugate D).map_pow (⟨c,1⟩ : QuadraticAlgebra K D 0) k
  exact h.symm

variable {α : Type} (ea : BitEncoding α)

theorem fp_unary_sub (f g : α → ℕ) (hf : FP ea BitEncoding.unaryNat f)
    (hg : FP ea BitEncoding.unaryNat g) :
    FP ea BitEncoding.unaryNat (fun x => f x-g x) := by
  have hb := ((hf.comp UnaryNatConversionMachine.fp_conversion).pair
    (hg.comp UnaryNatConversionMachine.fp_conversion)).comp BinaryArithmetic.fp_subtraction
  exact ((hf.pair hb).comp ⟨BoundedUnaryMachines.computer⟩).congr
    (fun x => min_eq_right (Nat.sub_le (f x) (g x)))

theorem fp_power_linear_plus (D : α → ℕ → K)
    (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n : ℕ) (i : Fin n) (c : α → K) (k : α → ℕ)
    (hc : FP ea (numberFieldEncoding basis) c) (hk : FP ea BitEncoding.unaryNat k) :
    FP ea (BooleanFieldTowerMachines.encoding basis n)
      (fun x => power (D x) n (linear n i (c x) 1) (k x)) := by
  have hq := (hk.pair (hc.pair (hD i.val))).comp
    (QuadraticBinomialPowerMachines.fp_quadraticPower_coefficients basis)
  have he := hq.comp (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  have ho := hq.comp (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))
  exact (BooleanFieldTowerMachines.fp_linear basis ea n i _ _ he ho).congr
    (fun x => (power_linear (D x) n i (c x) 1 (k x)).symm)

theorem fp_power_linear_minus (D : α → ℕ → K)
    (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n : ℕ) (i : Fin n) (c : α → K) (k : α → ℕ)
    (hc : FP ea (numberFieldEncoding basis) c) (hk : FP ea BitEncoding.unaryNat k) :
    FP ea (BooleanFieldTowerMachines.encoding basis n)
      (fun x => power (D x) n (linear n i (c x) (-1)) (k x)) := by
  have hq := (hk.pair (hc.pair (hD i.val))).comp
    (QuadraticBinomialPowerMachines.fp_quadraticPower_coefficients basis)
  have he := hq.comp (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  have ho := (hq.comp (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))).comp
    (FixedFieldArithmetic.fp_negation basis)
  apply (BooleanFieldTowerMachines.fp_linear basis ea n i _ _ he ho).congr
  intro x
  rw [power_linear,negative_branch_power]
  rfl

theorem fp_radicands {b : ℕ} (a w : Fin b → K) (x : α → K)
    (hx : FP ea (numberFieldEncoding basis) x) (i : ℕ) :
    FP ea (numberFieldEncoding basis) (fun y => radicands a w (x y) i) := by
  have hs := hx.comp (FixedFieldPolynomialMachines.fp_fixedPower basis 2)
  have hw := ((fp_const ea (numberFieldEncoding basis) (extend w i^2)).pair hs).comp
    (FixedFieldArithmetic.fp_multiplication basis)
  exact ((fp_const ea (numberFieldEncoding basis) (extend a i^2)).pair hw).comp
    (FixedFieldArithmetic.fp_addition basis)

/-- Unary exponents are charged literally in the input encoding. -/
theorem fp_spectral {b : ℕ} (c a w : Fin b → K) (x : α → K) (n k : α → Fin b → ℕ)
    (hx : FP ea (numberFieldEncoding basis) x)
    (hn : ∀ i, FP ea BitEncoding.unaryNat (fun y => n y i))
    (hk : ∀ i, FP ea BitEncoding.unaryNat (fun y => k y i)) :
    FP ea (BooleanFieldTowerMachines.encoding basis b) (fun y => spectral c a w (x y) (n y) (k y)) := by
  let D := fun y => radicands a w (x y)
  have hD : ∀ i, FP ea (numberFieldEncoding basis) (fun y => D y i) := fp_radicands basis ea a w x hx
  apply BooleanFieldTowerMachines.fp_product basis ea D hD b b
  intro i
  apply BooleanFieldTowerMachines.fp_mul basis ea D hD b
  · exact fp_power_linear_plus basis ea D hD b i (fun _ => c i) _
      (fp_const ea (numberFieldEncoding basis) (c i)) (fp_unary_sub ea _ _ (hn i) (hk i))
  · exact fp_power_linear_minus basis ea D hD b i (fun _ => c i) _
      (fp_const ea (numberFieldEncoding basis) (c i)) (hk i)

/-- A genuine fixed-field machine evaluates the norm, with polynomial bit
cost inherited from its concrete submachines and composition. -/
theorem fp_collision {b : ℕ} (c a w : Fin b → K) (x : α → K) (n k l : α → Fin b → ℕ)
    (hx : FP ea (numberFieldEncoding basis) x)
    (hn : ∀ i, FP ea BitEncoding.unaryNat (fun y => n y i))
    (hk : ∀ i, FP ea BitEncoding.unaryNat (fun y => k y i))
    (hl : ∀ i, FP ea BitEncoding.unaryNat (fun y => l y i)) :
    FP ea (numberFieldEncoding basis) (fun y => collision c a w (x y) (n y) (k y) (l y)) := by
  apply BooleanFieldTowerMachines.fp_norm basis ea (fun y => radicands a w (x y))
    (fp_radicands basis ea a w x hx) b
  exact BooleanFieldTowerMachines.fp_sub basis ea b _ _
    (fp_spectral basis ea c a w x n k hx hn hk) (fp_spectral basis ea c a w x n l hx hn hl)

/-- Concrete raw input: a unary cap, rational parameter, and three fixed
binary count vectors. Counts are clipped so the evaluator is total. -/
abbrev Input (b : ℕ) := ℕ × (ℚ × ((Fin b → ℕ) × ((Fin b → ℕ) × (Fin b → ℕ))))

def inputEncoding (b : ℕ) : BitEncoding (Input b) :=
  BitEncoding.unaryNat.prod (BitEncoding.rat.prod
    ((BitEncoding.nat.vector b).prod ((BitEncoding.nat.vector b).prod (BitEncoding.nat.vector b))))

def totals {b : ℕ} (p : Input b) (i : Fin b) : ℕ := min p.1 (p.2.2.1 i)
def leftCounts {b : ℕ} (p : Input b) (i : Fin b) : ℕ := min (totals p i) (p.2.2.2.1 i)
def rightCounts {b : ℕ} (p : Input b) (i : Fin b) : ℕ := min (totals p i) (p.2.2.2.2 i)

def evaluate {b : ℕ} (c a w : Fin b → K) (p : Input b) : K :=
  collision c a w (algebraMap ℚ K p.2.1) (totals p) (leftCounts p) (rightCounts p)

theorem fp_evaluate {b : ℕ} (c a w : Fin b → K) :
    FP (inputEncoding b) (numberFieldEncoding basis) (evaluate c a w) := by
  let ve := BitEncoding.nat.vector b
  let re := BitEncoding.rat.prod (ve.prod (ve.prod ve))
  have hcap := fp_fst BitEncoding.unaryNat re
  have hp := fp_snd BitEncoding.unaryNat re
  have hrat := hp.comp (fp_fst BitEncoding.rat (ve.prod (ve.prod ve)))
  have hv := hp.comp (fp_snd BitEncoding.rat (ve.prod (ve.prod ve)))
  have hn := hv.comp (fp_fst ve (ve.prod ve))
  have hkl := hv.comp (fp_snd ve (ve.prod ve))
  have hk := hkl.comp (fp_fst ve ve)
  have hl := hkl.comp (fp_snd ve ve)
  have htot (i : Fin b) := (hcap.pair (hn.comp (FixedVectorMachines.fp_coordinate BitEncoding.nat b i))).comp
    (show FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p : ℕ × ℕ => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  apply fp_collision basis (inputEncoding b) c a w _ _ _ _
    (hrat.comp (FixedFieldPolynomialMachines.fp_ratCast basis)) htot
  · intro i
    exact ((htot i).pair (hk.comp (FixedVectorMachines.fp_coordinate BitEncoding.nat b i))).comp
      ⟨BoundedUnaryMachines.computer⟩
  · intro i
    exact ((htot i).pair (hl.comp (FixedVectorMachines.fp_coordinate BitEncoding.nat b i))).comp
      ⟨BoundedUnaryMachines.computer⟩

/-- On the promised bounded count inputs this is exactly the frozen real
collision polynomial, not a differently clipped function. -/
theorem evaluate_spec {b : ℕ} (f : K →+* ℝ) (c a w : Fin b → K)
    (M : ℕ) (q : ℚ) (n k l : Fin b → ℕ) (hn : ∀ i, n i≤M)
    (hk : ∀ i, k i≤n i) (hl : ∀ i, l i≤n i) :
    f (evaluate c a w (M,(q,(n,(k,l)))))=
      (BooleanExceptionalPolynomial.collisionPolynomial
        (fun j => f (c j)) (fun j => f (a j)) (fun j => f (w j)) n k l).eval (q : ℝ) := by
  have ht : totals (M,(q,(n,(k,l))))=n := funext fun i => min_eq_right (hn i)
  have hkl : leftCounts (M,(q,(n,(k,l))))=k := by
    funext i
    simp only [leftCounts,ht,min_eq_right (hk i)]
  have hr : rightCounts (M,(q,(n,(k,l))))=l := by
    funext i
    simp only [rightCounts,ht,min_eq_right (hl i)]
  simp only [evaluate,ht,hkl,hr,collision_eval]
  congr 1
  simp

end PlanarHom.BooleanFieldCollisionMachines

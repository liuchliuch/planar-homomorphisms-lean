import PlanarHom.BooleanFieldTower
import Mathlib.Algebra.Ring.TransferInstance

/-! The represented squarefree tower is a commutative algebra. This construction
makes no irreducibility or independence assumption on its radicands. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerAlgebra
open BooleanFieldTower
variable {K : Type*} [CommRing K]

/-- A type synonym separating radical multiplication from product multiplication. -/
def Carrier (_D : ℕ → K) (n : ℕ) := Tower K n

/-- Interpret the stored coefficient tuple in its represented algebra. -/
def ofTower (D : ℕ → K) (n : ℕ) (p : Tower K n) : Carrier D n := p

def quadraticEquiv (D : ℕ → K) (n : ℕ) [Zero (Carrier D n)] :
    Carrier D (n+1) ≃ QuadraticAlgebra (Carrier D n) (embed n (D n)) 0 where
  toFun p := ⟨p.1,p.2⟩
  invFun p := (p.re,p.im)
  left_inv p := rfl
  right_inv p := by cases p; rfl

/-- Iteration of the usual quadratic commutative algebra. -/
def commRing (D : ℕ → K) : (n : ℕ) → CommRing (Carrier D n)
  | 0 => inferInstanceAs (CommRing K)
  | n+1 => letI := commRing D n; (quadraticEquiv D n).commRing

instance (D : ℕ → K) (n : ℕ) : CommRing (Carrier D n) := commRing D n

@[simp] theorem zero_eq (D : ℕ → K) (n : ℕ) :
    (0 : Carrier D n) = (zero n : Tower K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih ih

@[simp] theorem one_eq (D : ℕ → K) (n : ℕ) :
    (1 : Carrier D n) = (embed n 1 : Tower K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (zero_eq D n)

@[simp] theorem add_eq (D : ℕ → K) (n : ℕ) (p q : Carrier D n) :
    p+q = (add n p q : Tower K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih _ _) (ih _ _)

@[simp] theorem neg_eq (D : ℕ → K) (n : ℕ) (p : Carrier D n) :
    -p = (neg n p : Tower K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih _) (ih _)

@[simp] theorem sub_eq (D : ℕ → K) (n : ℕ) (p q : Carrier D n) :
    p-q = (sub n p q : Tower K n) := by
  rw [_root_.sub_eq_add_neg,add_eq,neg_eq]
  rfl

@[simp] theorem mul_eq (D : ℕ → K) (n : ℕ) (p q : Carrier D n) :
    p*q = (mul D n p q : Tower K n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a : Carrier D n := p.1
    let b : Carrier D n := p.2
    let c : Carrier D n := q.1
    let d : Carrier D n := q.2
    let z : Carrier D n := embed n (D n)
    change (a*c+z*b*d, a*d+b*c+(0 : Carrier D n)*b*d) = _
    simp only [MulZeroClass.zero_mul,_root_.add_zero,_root_.mul_assoc]
    simp only [add_eq,ih]
    rfl

@[simp] theorem pow_eq (D : ℕ → K) (n : ℕ) (p : Carrier D n) (k : ℕ) :
    p^k = (power D n p k : Tower K n) := by
  induction k with
  | zero => simpa only [pow_zero,power] using one_eq D n
  | succ k ih => rw [pow_succ,mul_eq,ih]; rfl

/-- The represented finite product agrees with the commutative-ring product. -/
theorem product_eq (D : ℕ → K) (n k : ℕ) (p : Fin k → Carrier D n) :
    (∏ i,p i) = (product D n k p : Tower K n) := by
  induction k with
  | zero => simp only [Fin.prod_univ_zero,one_eq,product]
  | succ k ih => rw [Fin.prod_univ_castSucc,mul_eq,ih]; rfl

theorem embed_injective (n : ℕ) : Function.Injective (embed n : K → Tower K n) := by
  induction n with
  | zero => exact fun _ _ h=>h
  | succ n ih => exact fun _ _ h=>ih (congrArg Prod.fst h)

instance (D : ℕ → K) (n : ℕ) [Nontrivial K] : Nontrivial (Carrier D n) :=
  ⟨⟨embed n 0,embed n 1,fun h=>zero_ne_one (embed_injective n h)⟩⟩

/-- Base scalars embed in the radical algebra. -/
def baseHom (D : ℕ → K) (n : ℕ) : K →+* Carrier D n where
  toFun := embed n
  map_zero' := (zero_eq D n).symm ▸ embed_zero n
  map_one' := (one_eq D n).symm
  map_add' a b := by rw [add_eq,← embed_add]
  map_mul' a b := by rw [mul_eq,← embed_mul]

instance (D : ℕ → K) (n : ℕ) : Algebra K (Carrier D n) :=
  (baseHom D n).toAlgebra

@[simp] theorem algebraMap_eq (D : ℕ → K) (n : ℕ) (c : K) :
    algebraMap K (Carrier D n) c = embed n c := rfl

end PlanarHom.BooleanFieldTowerAlgebra

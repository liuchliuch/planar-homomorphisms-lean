import PlanarHom.BooleanFieldTower
import PlanarHom.BooleanExceptionalPolynomial

/-! Exact fixed-field specialization of the frozen radical-elimination
polynomial. All computations below use only base-ring arithmetic. -/
noncomputable section
namespace PlanarHom.BooleanFieldCollision
open BooleanFieldTower

/-- Evaluate each polynomial coefficient while retaining the squarefree basis. -/
def specialize (x : ℝ) : (n : ℕ) → BooleanRadicalNorm.Tower n → Tower ℝ n
  | 0,p => p.eval x
  | n+1,p => (specialize x n p.1,specialize x n p.2)

@[simp] theorem specialize_zero (x : ℝ) (n : ℕ) :
    specialize x n (BooleanRadicalNorm.zero n)=zero n := by
  induction n with
  | zero => simp [specialize,BooleanRadicalNorm.zero,zero]
  | succ n ih => exact Prod.ext ih ih

@[simp] theorem specialize_embed (x : ℝ) (n : ℕ) (p : Polynomial ℝ) :
    specialize x n (BooleanRadicalNorm.embed n p)=embed n (p.eval x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [specialize,BooleanRadicalNorm.embed,embed,ih,specialize_zero]

@[simp] theorem specialize_add (x : ℝ) (n : ℕ) (p q : BooleanRadicalNorm.Tower n) :
    specialize x n (BooleanRadicalNorm.add n p q)=add n (specialize x n p) (specialize x n q) := by
  induction n with
  | zero => exact Polynomial.eval_add
  | succ n ih => exact Prod.ext (ih _ _) (ih _ _)

@[simp] theorem specialize_neg (x : ℝ) (n : ℕ) (p : BooleanRadicalNorm.Tower n) :
    specialize x n (BooleanRadicalNorm.neg n p)=neg n (specialize x n p) := by
  induction n with
  | zero => simp [specialize,BooleanRadicalNorm.neg,neg]
  | succ n ih => exact Prod.ext (ih _) (ih _)

@[simp] theorem specialize_sub (x : ℝ) (n : ℕ) (p q : BooleanRadicalNorm.Tower n) :
    specialize x n (BooleanRadicalNorm.sub n p q)=sub n (specialize x n p) (specialize x n q) := by
  simp [BooleanRadicalNorm.sub,sub]

@[simp] theorem specialize_mul (x : ℝ) (D : ℕ → Polynomial ℝ) (n : ℕ)
    (p q : BooleanRadicalNorm.Tower n) :
    specialize x n (BooleanRadicalNorm.mul D n p q)=
      mul (fun i => (D i).eval x) n (specialize x n p) (specialize x n q) := by
  induction n with
  | zero => exact Polynomial.eval_mul
  | succ n ih => simp only [specialize,BooleanRadicalNorm.mul,mul,specialize_add,specialize_embed,ih]

@[simp] theorem specialize_power (x : ℝ) (D : ℕ → Polynomial ℝ) (n : ℕ)
    (p : BooleanRadicalNorm.Tower n) (k : ℕ) :
    specialize x n (BooleanRadicalNorm.power D n p k)=
      power (fun i => (D i).eval x) n (specialize x n p) k := by
  induction k with
  | zero => simp [BooleanRadicalNorm.power,power]
  | succ k ih => simp only [BooleanRadicalNorm.power,power,specialize_mul,ih]

@[simp] theorem specialize_norm (x : ℝ) (D : ℕ → Polynomial ℝ) (n : ℕ)
    (p : BooleanRadicalNorm.Tower n) :
    (BooleanRadicalNorm.norm D n p).eval x=
      norm (fun i => (D i).eval x) n (specialize x n p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [BooleanRadicalNorm.norm,BooleanFieldTower.norm,ih,specialize_sub,specialize_mul,
      specialize_embed,specialize]

@[simp] theorem specialize_product (x : ℝ) (D : ℕ → Polynomial ℝ) (n k : ℕ)
    (p : Fin k → BooleanRadicalNorm.Tower n) :
    specialize x n (BooleanRadicalNorm.product D n k p)=
      product (fun i => (D i).eval x) n k (fun i => specialize x n (p i)) := by
  induction k with
  | zero => simp [BooleanRadicalNorm.product,product]
  | succ k ih => simp only [BooleanRadicalNorm.product,product,specialize_mul,ih]

@[simp] theorem specialize_radical (x : ℝ) (n : ℕ) (i : Fin n) :
    specialize x n (BooleanRadicalNorm.radical n i)=linear n i 0 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [BooleanRadicalNorm.radical,linear,specialize]
    · simp [BooleanRadicalNorm.radical,linear,specialize,ih]

variable {K L : Type*} [CommRing K]

@[simp] theorem add_linear (n : ℕ) (i : Fin n) (e o f p : K) :
    add n (linear n i e o) (linear n i f p)=linear n i (e+f) (o+p) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [linear,Fin.lastCases_last,add,← embed_add]
    · simp only [linear,Fin.lastCases_castSucc,add,ih,BooleanFieldTower.add_zero]

@[simp] theorem neg_linear (n : ℕ) (i : Fin n) (e o : K) :
    neg n (linear n i e o)=linear n i (-e) (-o) := by
  have hz (n : ℕ) : neg n (zero n : Tower K n)=zero n := by
    induction n with
    | zero => exact neg_zero
    | succ n ih => exact Prod.ext ih ih
  have he (n : ℕ) (e : K) : neg n (embed n e)=embed n (-e) := by
    induction n with
    | zero => rfl
    | succ n ih => exact Prod.ext ih (hz n)
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [linear,Fin.lastCases_last,neg,he]
    · simp only [linear,Fin.lastCases_castSucc,neg,ih,hz]

@[simp] theorem specialize_branchPlus {b : ℕ} (x : ℝ) (c : Fin b → ℝ) (i : Fin b) :
    specialize x b (BooleanExceptionalPolynomial.branchPlus c i)=linear b i (c i) 1 := by
  simp only [BooleanExceptionalPolynomial.branchPlus,specialize_add,specialize_embed,
    Polynomial.eval_C,specialize_radical]
  rw [← linear_zero_im b i (c i),add_linear]
  simp

@[simp] theorem specialize_branchMinus {b : ℕ} (x : ℝ) (c : Fin b → ℝ) (i : Fin b) :
    specialize x b (BooleanExceptionalPolynomial.branchMinus c i)=linear b i (c i) (-1) := by
  simp only [BooleanExceptionalPolynomial.branchMinus,specialize_sub,specialize_embed,
    Polynomial.eval_C,specialize_radical,sub,neg_linear,neg_zero]
  rw [← linear_zero_im b i (c i),add_linear]
  simp

/-- Extend finite field parameters with zero outside their actual range. -/
def extend {b : ℕ} (f : Fin b → K) (i : ℕ) : K := if h : i<b then f ⟨i,h⟩ else 0

@[simp] theorem extend_val {b : ℕ} (f : Fin b → K) (i : Fin b) : extend f i.val=f i := by
  simp [extend,i.isLt]

def radicands {b : ℕ} (a w : Fin b → K) (x : K) (i : ℕ) : K :=
  extend a i ^ 2 + extend w i ^ 2 * x^2

@[simp] theorem eval_radicand {b : ℕ} (a w : Fin b → ℝ) (x : ℝ) (i : ℕ) :
    (BooleanExceptionalPolynomial.radicand a w i).eval x=radicands a w x i := by
  simp [BooleanExceptionalPolynomial.radicand,BooleanExceptionalPolynomial.extend,radicands,extend]

def spectral {b : ℕ} (c a w : Fin b → K) (x : K) (n k : Fin b → ℕ) : Tower K b :=
  product (radicands a w x) b b fun i => mul (radicands a w x) b
    (power (radicands a w x) b (linear b i (c i) 1) (n i-k i))
    (power (radicands a w x) b (linear b i (c i) (-1)) (k i))

def collision {b : ℕ} (c a w : Fin b → K) (x : K) (n k l : Fin b → ℕ) : K :=
  norm (radicands a w x) b (sub b (spectral c a w x n k) (spectral c a w x n l))

@[simp] theorem specialize_spectral {b : ℕ} (c a w : Fin b → ℝ) (x : ℝ) (n k : Fin b → ℕ) :
    specialize x b (BooleanExceptionalPolynomial.spectralTower c a w n k)=spectral c a w x n k := by
  simp only [BooleanExceptionalPolynomial.spectralTower,specialize_product,specialize_mul,
    specialize_power,specialize_branchPlus,specialize_branchMinus,spectral,eval_radicand]

/-- Exact equality to evaluation of the frozen, genuinely nonzero eliminant. -/
theorem collision_real_eq {b : ℕ} (c a w : Fin b → ℝ) (x : ℝ) (n k l : Fin b → ℕ) :
    collision c a w x n k l=(BooleanExceptionalPolynomial.collisionPolynomial c a w n k l).eval x := by
  simp only [BooleanExceptionalPolynomial.collisionPolynomial,specialize_norm,specialize_sub,
    specialize_spectral,collision,eval_radicand]

variable [CommRing L]

@[simp] theorem map_extend (f : K →+* L) {b : ℕ} (a : Fin b → K) (i : ℕ) :
    f (extend a i)=extend (fun j => f (a j)) i := by
  unfold extend
  split <;> simp

@[simp] theorem map_radicands (f : K →+* L) {b : ℕ} (a w : Fin b → K) (x : K) (i : ℕ) :
    f (radicands a w x i)=radicands (fun j => f (a j)) (fun j => f (w j)) (f x) i := by
  simp [radicands]

@[simp] theorem map_spectral (f : K →+* L) {b : ℕ} (c a w : Fin b → K) (x : K) (n k : Fin b → ℕ) :
    map f b (spectral c a w x n k)=spectral (fun j => f (c j)) (fun j => f (a j))
      (fun j => f (w j)) (f x) n k := by
  simp only [spectral,map_product,BooleanFieldTower.map_mul,map_power,map_linear,map_one,_root_.map_neg,map_radicands]

@[simp] theorem map_collision (f : K →+* L) {b : ℕ} (c a w : Fin b → K) (x : K) (n k l : Fin b → ℕ) :
    f (collision c a w x n k l)=collision (fun j => f (c j)) (fun j => f (a j))
      (fun j => f (w j)) (f x) n k l := by
  simp only [collision,map_norm,BooleanFieldTower.map_sub,map_spectral,map_radicands]

/-- Any fixed real embedding carries the field computation to the literal
real polynomial evaluation. No radical value occurs in the computation. -/
theorem collision_eval {b : ℕ} (f : K →+* ℝ) (c a w : Fin b → K) (x : K) (n k l : Fin b → ℕ) :
    f (collision c a w x n k l)=
      (BooleanExceptionalPolynomial.collisionPolynomial
        (fun j => f (c j)) (fun j => f (a j)) (fun j => f (w j)) n k l).eval (f x) := by
  rw [map_collision,collision_real_eq]

end PlanarHom.BooleanFieldCollision

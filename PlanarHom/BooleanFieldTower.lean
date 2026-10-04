import PlanarHom.BooleanRadicalNorm
import Mathlib.Algebra.QuadraticAlgebra

/-! Fixed-dimensional radical arithmetic after specialization of the polynomial
variable. No square root operation is used: all leaves belong to the base ring. -/
noncomputable section
namespace PlanarHom.BooleanFieldTower

abbrev Tower (K : Type*) : ℕ → Type _
  | 0 => K
  | n+1 => Tower K n × Tower K n

variable {K L : Type*}

def zero [Zero K] : (n : ℕ) → Tower K n
  | 0 => 0
  | n+1 => (zero n,zero n)

def embed [Zero K] : (n : ℕ) → K → Tower K n
  | 0,c => c
  | n+1,c => (embed n c,zero n)

def add [Add K] : (n : ℕ) → Tower K n → Tower K n → Tower K n
  | 0,p,q => p+q
  | n+1,p,q => (add n p.1 q.1,add n p.2 q.2)

def neg [Neg K] : (n : ℕ) → Tower K n → Tower K n
  | 0,p => -p
  | n+1,p => (neg n p.1,neg n p.2)

def sub [Add K] [Neg K] (n : ℕ) (p q : Tower K n) : Tower K n := add n p (neg n q)

def mul [Zero K] [Add K] [Mul K] (D : ℕ → K) :
    (n : ℕ) → Tower K n → Tower K n → Tower K n
  | 0,p,q => p*q
  | n+1,p,q =>
    (add n (mul D n p.1 q.1) (mul D n (embed n (D n)) (mul D n p.2 q.2)),
     add n (mul D n p.1 q.2) (mul D n p.2 q.1))

def power [Zero K] [One K] [Add K] [Mul K] (D : ℕ → K) (n : ℕ) (p : Tower K n) : ℕ → Tower K n
  | 0 => embed n 1
  | k+1 => mul D n (power D n p k) p

def norm [Zero K] [Add K] [Neg K] [Mul K] (D : ℕ → K) : (n : ℕ) → Tower K n → K
  | 0,p => p
  | n+1,p => norm D n (sub n (mul D n p.1 p.1)
      (mul D n (embed n (D n)) (mul D n p.2 p.2)))

def product [Zero K] [One K] [Add K] [Mul K] (D : ℕ → K) (n : ℕ) :
    (k : ℕ) → (Fin k → Tower K n) → Tower K n
  | 0,_ => embed n 1
  | k+1,f => mul D n (product D n k (fun i => f i.castSucc)) (f (Fin.last k))

/-- A pair `e+o*r_i` placed in the `i`-th radical direction. -/
def linear [Zero K] : (n : ℕ) → Fin n → K → K → Tower K n
  | n+1,i,e,o => Fin.lastCases (embed n e,embed n o)
      (fun j => (linear n j e o,zero n)) i

section Ring
variable [CommRing K]

@[simp] theorem add_zero (n : ℕ) (p : Tower K n) : add n p (zero n)=p := by
  induction n with
  | zero => exact _root_.add_zero _
  | succ n ih => exact Prod.ext (ih _) (ih _)

@[simp] theorem zero_add (n : ℕ) (p : Tower K n) : add n (zero n) p=p := by
  induction n with
  | zero => exact _root_.zero_add _
  | succ n ih => exact Prod.ext (ih _) (ih _)

@[simp] theorem mul_zero (D : ℕ → K) (n : ℕ) (p : Tower K n) : mul D n p (zero n)=zero n := by
  induction n with
  | zero => exact MulZeroClass.mul_zero _
  | succ n ih => simp only [mul,zero,ih,add_zero]

@[simp] theorem zero_mul (D : ℕ → K) (n : ℕ) (p : Tower K n) : mul D n (zero n) p=zero n := by
  induction n with
  | zero => exact MulZeroClass.zero_mul _
  | succ n ih => simp only [mul,zero,ih,mul_zero,add_zero]

@[simp] theorem embed_zero (n : ℕ) : embed n (0 : K)=zero n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih rfl

@[simp] theorem embed_add (n : ℕ) (a b : K) : embed n (a+b)=add n (embed n a) (embed n b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [embed,add,ih,add_zero]

@[simp] theorem embed_mul (D : ℕ → K) (n : ℕ) (a b : K) :
    embed n (a*b)=mul D n (embed n a) (embed n b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [embed,mul,ih,mul_zero,zero_mul,add_zero]

@[simp] theorem linear_zero_im (n : ℕ) (i : Fin n) (e : K) :
    linear n i e 0=embed n e := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [linear,embed]
    · simp [linear,ih,embed]

/-- Reduced multiplication in one radical agrees with its actual quadratic
algebra, including dependent or square radicands. -/
theorem mul_linear (D : ℕ → K) (n : ℕ) (i : Fin n) (e o f p : K) :
    mul D n (linear n i e o) (linear n i f p) =
      linear n i (e*f+D i.val*o*p) (e*p+o*f) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [linear,Fin.lastCases_last,mul,Fin.val_last,← embed_mul,← embed_add]
      congr 2
      ring
    · simp only [linear,Fin.lastCases_castSucc,mul,mul_zero,zero_mul,add_zero,Fin.coe_castSucc,ih]

/-- The variable-length power is exactly the two binomial coefficients of
one quadratic algebra inserted into the selected radical coordinate. -/
theorem power_linear (D : ℕ → K) (n : ℕ) (i : Fin n) (e o : K) (k : ℕ) :
    power D n (linear n i e o) k =
      linear n i ((QuadraticAlgebra.mk e o : QuadraticAlgebra K (D i.val) 0)^k).re
        ((QuadraticAlgebra.mk e o : QuadraticAlgebra K (D i.val) 0)^k).im := by
  induction k with
  | zero => simpa only [power,pow_zero,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] using
      (linear_zero_im n i (1 : K)).symm
  | succ k ih =>
    rw [power,ih,mul_linear,pow_succ]
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,MulZeroClass.zero_mul,_root_.add_zero]

end Ring

section Map
variable [CommRing K] [CommRing L]

def map (f : K →+* L) : (n : ℕ) → Tower K n → Tower L n
  | 0,p => f p
  | n+1,p => (map f n p.1,map f n p.2)

@[simp] theorem map_zero (f : K →+* L) (n : ℕ) : map f n (zero n)=zero n := by
  induction n with
  | zero => exact f.map_zero
  | succ n ih => exact Prod.ext ih ih

@[simp] theorem map_embed (f : K →+* L) (n : ℕ) (c : K) : map f n (embed n c)=embed n (f c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [map,embed,ih,map_zero]

@[simp] theorem map_add (f : K →+* L) (n : ℕ) (p q : Tower K n) :
    map f n (add n p q)=add n (map f n p) (map f n q) := by
  induction n with
  | zero => exact f.map_add _ _
  | succ n ih => exact Prod.ext (ih _ _) (ih _ _)

@[simp] theorem map_neg (f : K →+* L) (n : ℕ) (p : Tower K n) :
    map f n (neg n p)=neg n (map f n p) := by
  induction n with
  | zero => exact f.map_neg _
  | succ n ih => exact Prod.ext (ih _) (ih _)

@[simp] theorem map_sub (f : K →+* L) (n : ℕ) (p q : Tower K n) :
    map f n (sub n p q)=sub n (map f n p) (map f n q) := by simp [sub]

@[simp] theorem map_mul (f : K →+* L) (D : ℕ → K) (n : ℕ) (p q : Tower K n) :
    map f n (mul D n p q)=mul (fun i => f (D i)) n (map f n p) (map f n q) := by
  induction n with
  | zero => exact f.map_mul _ _
  | succ n ih => simp only [map,mul,map_add,map_embed,ih]

@[simp] theorem map_power (f : K →+* L) (D : ℕ → K) (n : ℕ) (p : Tower K n) (k : ℕ) :
    map f n (power D n p k)=power (fun i => f (D i)) n (map f n p) k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp only [power,map_mul,ih]

@[simp] theorem map_norm (f : K →+* L) (D : ℕ → K) (n : ℕ) (p : Tower K n) :
    f (norm D n p)=norm (fun i => f (D i)) n (map f n p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [norm,ih,map_sub,map_mul,map_embed,map]

@[simp] theorem map_product (f : K →+* L) (D : ℕ → K) (n k : ℕ) (p : Fin k → Tower K n) :
    map f n (product D n k p)=product (fun i => f (D i)) n k (fun i => map f n (p i)) := by
  induction k with
  | zero => simp [product]
  | succ k ih => simp only [product,map_mul,ih]

@[simp] theorem map_linear (f : K →+* L) (n : ℕ) (i : Fin n) (e o : K) :
    map f n (linear n i e o)=linear n i (f e) (f o) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [linear,map]
    · simp [linear,map,ih]

end Map
end PlanarHom.BooleanFieldTower

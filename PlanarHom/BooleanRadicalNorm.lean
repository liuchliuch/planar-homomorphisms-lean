import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Explicit elimination of a fixed number of square roots

A polynomial radical tower is represented in the squarefree basis. The
recursive norm multiplies the two signs of the last radical, successively
removing every radical. All coefficients are actual real polynomials.
-/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanRadicalNorm

/-- Squarefree expressions in `n` formal square roots. -/
abbrev Tower : ℕ → Type
  | 0 => Polynomial ℝ
  | n+1 => Tower n × Tower n

def zero : (n : ℕ) → Tower n
  | 0 => 0
  | n+1 => (zero n, zero n)

def embed : (n : ℕ) → Polynomial ℝ → Tower n
  | 0, p => p
  | n+1, p => (embed n p, zero n)

def add : (n : ℕ) → Tower n → Tower n → Tower n
  | 0, p, q => p+q
  | n+1, p, q => (add n p.1 q.1, add n p.2 q.2)

def neg : (n : ℕ) → Tower n → Tower n
  | 0, p => -p
  | n+1, p => (neg n p.1, neg n p.2)

def sub (n : ℕ) (p q : Tower n) : Tower n := add n p (neg n q)

/-- Multiplication reduced by the equations `root_i² = D_i`. -/
def mul (D : ℕ → Polynomial ℝ) : (n : ℕ) → Tower n → Tower n → Tower n
  | 0, p, q => p*q
  | n+1, p, q =>
    (add n (mul D n p.1 q.1) (mul D n (embed n (D n)) (mul D n p.2 q.2)),
     add n (mul D n p.1 q.2) (mul D n p.2 q.1))

def power (D : ℕ → Polynomial ℝ) (n : ℕ) (p : Tower n) : ℕ → Tower n
  | 0 => embed n 1
  | k+1 => mul D n (power D n p k) p

/-- A weighted degree bound: each radical has weight one. The signed
integer bound permits the zero coefficient below degree zero. -/
def Bounded : (n : ℕ) → Tower n → ℤ → Prop
  | 0, p, d => p=0 ∨ (p.natDegree : ℤ)≤d
  | n+1, p, d => Bounded n p.1 d ∧ Bounded n p.2 (d-1)

theorem bounded_zero (n : ℕ) (d : ℤ) : Bounded n (zero n) d := by
  induction n generalizing d with
  | zero => exact Or.inl rfl
  | succ n ih => exact ⟨ih d, ih (d-1)⟩

theorem bounded_embed (n : ℕ) (p : Polynomial ℝ) (d : ℤ)
    (hp : p=0 ∨ (p.natDegree : ℤ)≤d) : Bounded n (embed n p) d := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ⟨ih, bounded_zero n (d-1)⟩

theorem Bounded.mono {n : ℕ} {p : Tower n} {d e : ℤ}
    (hp : Bounded n p d) (hde : d≤e) : Bounded n p e := by
  induction n generalizing d e with
  | zero => exact hp.imp_right (fun h => h.trans hde)
  | succ n ih => exact ⟨ih hp.1 hde, ih hp.2 (by omega)⟩

theorem bounded_add {n : ℕ} {p q : Tower n} {d : ℤ}
    (hp : Bounded n p d) (hq : Bounded n q d) : Bounded n (add n p q) d := by
  induction n generalizing d with
  | zero =>
    rcases hp with rfl|hp
    · simpa [add] using hq
    rcases hq with rfl|hq
    · simpa [add] using (Or.inr hp : Bounded 0 p d)
    right
    exact le_trans (by exact_mod_cast Polynomial.natDegree_add_le p q) (max_le hp hq)
  | succ n ih => exact ⟨ih hp.1 hq.1, ih hp.2 hq.2⟩

theorem bounded_neg {n : ℕ} {p : Tower n} {d : ℤ}
    (hp : Bounded n p d) : Bounded n (neg n p) d := by
  induction n generalizing d with
  | zero => simpa [Bounded, neg] using hp
  | succ n ih => exact ⟨ih hp.1, ih hp.2⟩

theorem bounded_sub {n : ℕ} {p q : Tower n} {d : ℤ}
    (hp : Bounded n p d) (hq : Bounded n q d) : Bounded n (sub n p q) d :=
  bounded_add hp (bounded_neg hq)

theorem bounded_mul (D : ℕ → Polynomial ℝ) (hD : ∀ i, (D i).natDegree≤2)
    {n : ℕ} {p q : Tower n} {d e : ℤ}
    (hp : Bounded n p d) (hq : Bounded n q e) :
    Bounded n (mul D n p q) (d+e) := by
  induction n generalizing d e with
  | zero =>
    rcases hp with rfl|hp
    · exact Or.inl (zero_mul _)
    rcases hq with rfl|hq
    · exact Or.inl (mul_zero _)
    right
    exact le_trans (by exact_mod_cast (Polynomial.natDegree_mul_le (p := p) (q := q))) (add_le_add hp hq)
  | succ n ih =>
    have hrad : Bounded n (embed n (D n)) 2 :=
      bounded_embed n (D n) 2 (Or.inr (by exact_mod_cast hD n))
    refine ⟨bounded_add (ih hp.1 hq.1) ?_, bounded_add ?_ ?_⟩
    · convert ih hrad (ih hp.2 hq.2) using 1; ring
    · convert ih hp.1 hq.2 using 1; ring
    · convert ih hp.2 hq.1 using 1; ring

/-- The actual iterated polynomial norm; no abstract field extension is
assumed in its construction. -/
def norm (D : ℕ → Polynomial ℝ) : (n : ℕ) → Tower n → Polynomial ℝ
  | 0, p => p
  | n+1, p => norm D n (sub n (mul D n p.1 p.1)
      (mul D n (embed n (D n)) (mul D n p.2 p.2)))

theorem bounded_norm (D : ℕ → Polynomial ℝ) (hD : ∀ i, (D i).natDegree≤2)
    {n : ℕ} {p : Tower n} {d : ℤ} (hp : Bounded n p d) :
    norm D n p=0 ∨ ((norm D n p).natDegree : ℤ)≤2^n*d := by
  induction n generalizing d with
  | zero => simpa [norm] using hp
  | succ n ih =>
    have hrad : Bounded n (embed n (D n)) 2 :=
      bounded_embed n (D n) 2 (Or.inr (by exact_mod_cast hD n))
    have hleft := bounded_mul D hD hp.1 hp.1
    have hright := bounded_mul D hD hrad (bounded_mul D hD hp.2 hp.2)
    have hh : Bounded n (sub n (mul D n p.1 p.1)
      (mul D n (embed n (D n)) (mul D n p.2 p.2))) (2*d) := by
      apply bounded_sub
      · convert hleft using 1; ring
      · convert hright using 1; ring
    have h := ih hh
    simpa only [norm, pow_succ, mul_assoc, mul_left_comm 2] using h

/-- Evaluation at an independently chosen sign of each real radical. -/
def eval : (n : ℕ) → Tower n → ℝ → (ℕ → ℝ) → (Fin n → Bool) → ℝ
  | 0, p, x, _, _ => p.eval x
  | n+1, p, x, r, σ =>
    eval n p.1 x r (fun i => σ i.castSucc) +
      (if σ (Fin.last n) then -(r n) else r n) * eval n p.2 x r (fun i => σ i.castSucc)

@[simp] theorem eval_zero (n : ℕ) (x : ℝ) (r : ℕ → ℝ) (σ : Fin n → Bool) :
    eval n (zero n) x r σ=0 := by
  induction n with
  | zero => simp [eval, zero]
  | succ n ih => simp [eval, zero, ih]

@[simp] theorem eval_embed (n : ℕ) (p : Polynomial ℝ) (x : ℝ)
    (r : ℕ → ℝ) (σ : Fin n → Bool) : eval n (embed n p) x r σ=p.eval x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eval, embed, ih]

@[simp] theorem eval_add (n : ℕ) (p q : Tower n) (x : ℝ)
    (r : ℕ → ℝ) (σ : Fin n → Bool) :
    eval n (add n p q) x r σ=eval n p x r σ+eval n q x r σ := by
  induction n with
  | zero => exact Polynomial.eval_add
  | succ n ih => simp only [eval, add, ih]; ring

@[simp] theorem eval_neg (n : ℕ) (p : Tower n) (x : ℝ)
    (r : ℕ → ℝ) (σ : Fin n → Bool) :
    eval n (neg n p) x r σ = -eval n p x r σ := by
  induction n with
  | zero => simp [eval, neg]
  | succ n ih => simp only [eval, neg, ih]; ring

@[simp] theorem eval_sub (n : ℕ) (p q : Tower n) (x : ℝ)
    (r : ℕ → ℝ) (σ : Fin n → Bool) :
    eval n (sub n p q) x r σ=eval n p x r σ-eval n q x r σ := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem eval_mul (D : ℕ → Polynomial ℝ) (n : ℕ) (p q : Tower n)
    (x : ℝ) (r : ℕ → ℝ) (hr : ∀ i, r i^2=(D i).eval x) (σ : Fin n → Bool) :
    eval n (mul D n p q) x r σ=eval n p x r σ*eval n q x r σ := by
  induction n with
  | zero => exact Polynomial.eval_mul
  | succ n ih =>
    simp only [mul, eval, eval_add, eval_embed, ih]
    rw [← hr n]
    cases σ (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The iterated norm vanishes at exactly the union of the zeros of all
sign conjugates, even when some radicands are squares or dependent. -/
theorem eval_norm_ne_zero_iff (D : ℕ → Polynomial ℝ) (n : ℕ) (p : Tower n)
    (x : ℝ) (r : ℕ → ℝ) (hr : ∀ i, r i^2=(D i).eval x) :
    (norm D n p).eval x≠0 ↔ ∀ σ : Fin n → Bool, eval n p x r σ≠0 := by
  induction n with
  | zero => simp [norm, eval]
  | succ n ih =>
    rw [norm, ih]
    simp only [eval_sub, eval_mul D n _ _ x r hr, eval_embed]
    have hfactor (σ : Fin n → Bool) :
        eval n p.1 x r σ * eval n p.1 x r σ -
          (D n).eval x * (eval n p.2 x r σ * eval n p.2 x r σ) =
        (eval n p.1 x r σ + r n * eval n p.2 x r σ) *
          (eval n p.1 x r σ - r n * eval n p.2 x r σ) := by
      rw [← hr n]
      ring
    simp only [hfactor, mul_ne_zero_iff]
    constructor
    · intro h σ
      have hh := h (fun i => σ i.castSucc)
      change _ + (if σ (Fin.last n) then -(r n) else r n) * _ ≠ 0
      cases σ (Fin.last n) with
      | false => exact hh.1
      | true => simpa only [↓reduceIte, neg_mul, ← sub_eq_add_neg] using hh.2
    · intro h σ
      constructor
      · simpa [eval] using h (Fin.snoc σ false)
      · simpa [eval, neg_mul, ← sub_eq_add_neg] using h (Fin.snoc σ true)

/-- The `i`-th square root in the squarefree basis. -/
def radical : (n : ℕ) → Fin n → Tower n
  | n+1, i => Fin.lastCases (zero n, embed n 1)
      (fun j => (radical n j, zero n)) i

@[simp] theorem eval_radical (n : ℕ) (i : Fin n) (x : ℝ)
    (r : ℕ → ℝ) (σ : Fin n → Bool) :
    eval n (radical n i) x r σ = if σ i then -(r i.val) else r i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [radical, eval]
    · simp [radical, eval, ih]

theorem bounded_radical (n : ℕ) (i : Fin n) : Bounded n (radical n i) 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [radical, Fin.lastCases_last, Bounded]
      exact ⟨bounded_zero _ _, bounded_embed _ _ _ (Or.inr (by simp))⟩
    · simpa only [radical, Fin.lastCases_castSucc, Bounded] using
        And.intro (ih j) (bounded_zero n (1-1))

@[simp] theorem eval_power (D : ℕ → Polynomial ℝ) (n : ℕ) (p : Tower n)
    (k : ℕ) (x : ℝ) (r : ℕ → ℝ) (hr : ∀ i, r i^2=(D i).eval x)
    (σ : Fin n → Bool) : eval n (power D n p k) x r σ=eval n p x r σ^k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp only [power, eval_mul D n _ _ x r hr, ih, pow_succ]

theorem bounded_power (D : ℕ → Polynomial ℝ) (hD : ∀ i, (D i).natDegree≤2)
    {n : ℕ} {p : Tower n} {d : ℤ} (hp : Bounded n p d) (k : ℕ) :
    Bounded n (power D n p k) (k*d) := by
  induction k with
  | zero => exact bounded_embed _ _ _ (Or.inr (by simp))
  | succ k ih =>
    convert bounded_mul D hD ih hp using 1
    push_cast
    ring

/-- A finite product implemented by successive reduced multiplication. -/
def product (D : ℕ → Polynomial ℝ) (n : ℕ) : (k : ℕ) → (Fin k → Tower n) → Tower n
  | 0, _ => embed n 1
  | k+1, f => mul D n (product D n k (fun i => f i.castSucc)) (f (Fin.last k))

@[simp] theorem eval_product (D : ℕ → Polynomial ℝ) (n k : ℕ) (f : Fin k → Tower n)
    (x : ℝ) (r : ℕ → ℝ) (hr : ∀ i, r i^2=(D i).eval x) (σ : Fin n → Bool) :
    eval n (product D n k f) x r σ=∏ i, eval n (f i) x r σ := by
  induction k with
  | zero => simp [product]
  | succ k ih => simp only [product, eval_mul D n _ _ x r hr, ih, Fin.prod_univ_castSucc]

theorem bounded_product (D : ℕ → Polynomial ℝ) (hD : ∀ i, (D i).natDegree≤2)
    (n k : ℕ) (f : Fin k → Tower n) (d : Fin k → ℤ) (hf : ∀ i, Bounded n (f i) (d i)) :
    Bounded n (product D n k f) (∑ i, d i) := by
  induction k with
  | zero => exact bounded_embed _ _ _ (Or.inr (by simp))
  | succ k ih =>
    simpa only [product, Fin.sum_univ_castSucc] using
      bounded_mul D hD (ih (fun i => f i.castSucc) (fun i => d i.castSucc)
        (fun i => hf i.castSucc)) (hf (Fin.last k))

end PlanarHom.BooleanRadicalNorm

import PlanarHom.BooleanFieldTowerAlgebra
import PlanarHom.BooleanFieldTowerMachines
import Mathlib.LinearAlgebra.Pi

/-! Fixed-dimensional coordinates for represented radical multiplication. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerLinearization
open BooleanFieldTower BooleanFieldTowerAlgebra
open scoped BigOperators

/-- Recursive squarefree monomial indices. -/
def Index : ℕ → Type
  | 0 => Unit
  | n+1 => Index n ⊕ Index n

instance indexFintype : (n : ℕ) → Fintype (Index n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := indexFintype n; inferInstanceAs (Fintype (Index n ⊕ Index n))

instance indexDecidableEq : (n : ℕ) → DecidableEq (Index n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => letI := indexDecidableEq n; inferInstanceAs (DecidableEq (Index n ⊕ Index n))

theorem index_card (n : ℕ) : Fintype.card (Index n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Index n ⊕ Index n)=_
    rw [Fintype.card_sum,ih,pow_succ]
    omega

variable {K : Type*}

/-- The coefficient of one squarefree monomial. -/
def coord : (n : ℕ) → Tower K n → Index n → K
  | 0,p,_ => p
  | n+1,p,.inl i => coord n p.1 i
  | n+1,p,.inr i => coord n p.2 i

/-- Assemble a coefficient tuple without any assumption on the radicands. -/
def assemble : (n : ℕ) → (Index n → K) → Tower K n
  | 0,f => f ()
  | n+1,f => (assemble n (fun i=>f (.inl i)),assemble n (fun i=>f (.inr i)))

@[simp] theorem coord_assemble (n : ℕ) (f : Index n → K) (i : Index n) :
    coord n (assemble n f) i=f i := by
  induction n with
  | zero => cases i; rfl
  | succ n ih => cases i <;> simp only [assemble,coord,ih]

@[simp] theorem assemble_coord (n : ℕ) (p : Tower K n) :
    assemble n (coord n p)=p := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih _) (ih _)

theorem coord_ext (n : ℕ) (p q : Tower K n)
    (h : ∀ i,coord n p i=coord n q i) : p=q := by
  rw [← assemble_coord n p,← assemble_coord n q]
  exact congrArg (assemble n) (funext h)

section Algebra
variable [CommRing K]

/-- The monomial with coefficient one at a single coordinate. -/
def atomic (n : ℕ) (i : Index n) : Tower K n :=
  assemble n (fun j=>if i=j then 1 else 0)

@[simp] theorem coord_atomic (n : ℕ) (i j : Index n) :
    coord n (atomic n i : Tower K n) j=if i=j then 1 else 0 := by
  simp [atomic]

@[simp] theorem coord_zero (n : ℕ) (i : Index n) :
    coord n (zero n : Tower K n) i=0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases i <;> simp only [zero,coord,ih]

@[simp] theorem coord_add (n : ℕ) (p q : Tower K n) (i : Index n) :
    coord n (add n p q) i=coord n p i+coord n q i := by
  induction n with
  | zero => rfl
  | succ n ih => cases i <;> simp only [add,coord,ih]

/-- Multiplication by an embedded scalar acts independently on every coordinate. -/
theorem coord_embed_mul (D : ℕ → K) (n : ℕ) (c : K) (p : Tower K n) (i : Index n) :
    coord n (mul D n (embed n c) p) i=c*coord n p i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i <;> simp only [mul,embed,BooleanFieldTower.zero_mul,BooleanFieldTower.mul_zero,BooleanFieldTower.add_zero,coord,ih]

@[simp] theorem coord_smul (D : ℕ → K) (n : ℕ) (c : K)
    (p : Carrier D n) (i : Index n) :
    coord n (c • p : Carrier D n) i=c*coord n p i := by
  rw [Algebra.smul_def,algebraMap_eq,mul_eq]
  exact coord_embed_mul D n c p i

/-- A coordinate projection is a linear map from the represented algebra. -/
def coordLinear (D : ℕ → K) (n : ℕ) (i : Index n) : Carrier D n →ₗ[K] K where
  toFun p := coord n p i
  map_add' p q := by rw [add_eq,coord_add]
  map_smul' c p := by simpa only [smul_eq_mul] using coord_smul D n c p i

@[simp] theorem coord_sum (D : ℕ → K) (n : ℕ) {J : Type*}
    (s : Finset J) (f : J → Carrier D n) (i : Index n) :
    coord n (∑ j ∈ s,f j : Carrier D n) i=∑ j ∈ s,coord n (f j) i :=
  map_sum (coordLinear D n i) f s

/-- Every represented element is a sum of its scalar-weighted monomials. -/
theorem coordinate_expansion (D : ℕ → K) (n : ℕ) (p : Carrier D n) :
    p=(∑ j : Index n,coord n p j • ofTower D n (atomic n j) : Carrier D n) := by
  apply coord_ext n
  intro i
  rw [coord_sum]
  simp only [coord_smul,ofTower,coord_atomic]
  simp

/-- The finite matrix of right multiplication by a fixed represented element. -/
def multiplicationMatrix (D : ℕ → K) (n : ℕ) (q : Tower K n) : Index n → Index n → K :=
  fun i j=>coord n (mul D n (atomic n j) q) i

/-- Right multiplication is a linear endomorphism of the represented algebra. -/
def rightMulLinear (D : ℕ → K) (n : ℕ) (q : Tower K n) :
    Carrier D n →ₗ[K] Carrier D n where
  toFun p := p * ofTower D n q
  map_add' p r := _root_.add_mul p r _
  map_smul' c p := smul_mul_assoc c p _

/-- Multiplication is linear in the left accumulator, even for dependent radicals. -/
theorem coord_mul (D : ℕ → K) (n : ℕ) (p q : Tower K n) (i : Index n) :
    coord n (mul D n p q) i=
      ∑ j : Index n,coord n p j * coord n (mul D n (atomic n j) q) i := by
  have he := coordinate_expansion D n (p : Carrier D n)
  have hm : ofTower D n p * ofTower D n q = mul D n p q := mul_eq D n _ _
  rw [← hm]
  rw [show ofTower D n p = _ from he,Finset.sum_mul,coord_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc,coord_smul,mul_eq]
  rfl

theorem coord_mul_matrix (D : ℕ → K) (n : ℕ) (p q : Tower K n) (i : Index n) :
    coord n (mul D n p q) i=
      ∑ j : Index n,coord n p j * multiplicationMatrix D n q i j :=
  coord_mul D n p q i

end Algebra

section Encoding
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines BooleanFieldTowerMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Extracting any fixed coefficient is polynomial time. -/
theorem fp_coord (n : ℕ) (i : Index n) :
    FP (encoding basis n) (numberFieldEncoding basis) (fun p=>coord n p i) := by
  induction n with
  | zero => exact fp_id _
  | succ n ih =>
    cases i with
    | inl i => exact (fp_fst (encoding basis n) (encoding basis n)).comp (ih i)
    | inr i => exact (fp_snd (encoding basis n) (encoding basis n)).comp (ih i)

/-- Coordinatewise polynomial-time data can be assembled into a fixed tower. -/
theorem fp_assemble {α : Type} (ea : BitEncoding α) (n : ℕ)
    (f : α → Index n → K)
    (hf : ∀ i,FP ea (numberFieldEncoding basis) (fun x=>f x i)) :
    FP ea (encoding basis n) (fun x=>assemble n (f x)) := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact (ih (fun x i=>f x (.inl i)) (fun i=>hf (.inl i))).pair
      (ih (fun x i=>f x (.inr i)) (fun i=>hf (.inr i)))

/-- The entries of multiplication matrices are polynomial-time functions of their data. -/
theorem fp_multiplicationMatrix {α : Type} (ea : BitEncoding α)
    (D : α → ℕ → K) (hD : ∀ k,FP ea (numberFieldEncoding basis) (fun x=>D x k))
    (n : ℕ) (q : α → Tower K n) (hq : FP ea (encoding basis n) q)
    (i j : Index n) :
    FP ea (numberFieldEncoding basis) (fun x=>multiplicationMatrix (D x) n (q x) i j) :=
  (fp_mul basis ea D hD n (fun _=>atomic n j) q
    (fp_const ea (encoding basis n) (atomic n j)) hq).comp (fp_coord basis n i)

/-- A leaf coefficient never has a longer encoding than its whole tower. -/
theorem coord_length_le (n : ℕ) (p : Tower K n) (i : Index n) :
    ((numberFieldEncoding basis).encode (coord n p i)).length≤
      ((encoding basis n).encode p).length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [encoding,BitEncoding.prod_length]
    cases i with
    | inl i => exact (ih p.1 i).trans (by omega)
    | inr i => exact (ih p.2 i).trans (by omega)

/-- A uniform coefficient bound controls the fixed-dimensional tuple encoding. -/
theorem encoding_length_le (n : ℕ) (p : Tower K n) (B : ℕ)
    (h : ∀ i,((numberFieldEncoding basis).encode (coord n p i)).length≤B) :
    ((encoding basis n).encode p).length+1≤4^n*(B+1) := by
  induction n with
  | zero => simpa using Nat.add_le_add_right (h ()) 1
  | succ n ih =>
    have hl := ih p.1 (fun i=>h (.inl i))
    have hr := ih p.2 (fun i=>h (.inr i))
    simp only [encoding,BitEncoding.prod_length,pow_succ]
    nlinarith

/-- The maximum coefficient encoding length. -/
def maxCoordLength (n : ℕ) (p : Tower K n) : ℕ :=
  Finset.univ.sup (fun i=>((numberFieldEncoding basis).encode (coord n p i)).length)

theorem maxCoordLength_le (n : ℕ) (p : Tower K n) :
    maxCoordLength basis n p≤((encoding basis n).encode p).length := by
  apply Finset.sup_le
  intro i _
  exact coord_length_le basis n p i

theorem encoding_length_le_max (n : ℕ) (p : Tower K n) :
    ((encoding basis n).encode p).length+1≤4^n*(maxCoordLength basis n p+1) := by
  apply encoding_length_le
  intro i
  exact Finset.le_sup (f := fun i=>((numberFieldEncoding basis).encode (coord n p i)).length) (Finset.mem_univ i)

end Encoding
end PlanarHom.BooleanFieldTowerLinearization

import PlanarHom.BooleanSpectralProjectors
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal Boolean tensor spectral expansions over arbitrary commutative rings.
In particular the statements apply to the represented radical algebra without
assuming that its radicals are independent or that it is a field. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorSpectral
variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

def tensor (A : ι→Matrix Bool Bool R) : Matrix (ι→Bool) (ι→Bool) R :=
  fun z w=>∏i,A i (z i) (w i)

theorem tensor_mul (A B : ι→Matrix Bool Bool R) :
    tensor A*tensor B=tensor (fun i=>A i*B i) := by
  ext z w
  simp only [tensor,Matrix.mul_apply,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b=>A i (z i) b*B i b (w i))).symm

omit [DecidableEq ι] in
@[simp] theorem tensor_one : tensor (fun _ : ι=>(1 : Matrix Bool Bool R))=1 := by
  ext z w
  by_cases h:z=w
  · subst w; simp [tensor]
  · rw [Matrix.one_apply_ne h]
    obtain ⟨i,hi⟩:=Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem tensor_pow (A : ι→Matrix Bool Bool R) (n : ℕ) :
    (tensor A)^n=tensor (fun i=>(A i)^n) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,ih,tensor_mul]; simp only [pow_succ]

omit [DecidableEq ι] in
theorem tensor_scalar (a : ι→R) (A : ι→Matrix Bool Bool R) :
    tensor (fun i=>a i • A i)=(∏i,a i) • tensor A := by
  ext z w
  simp [tensor,Finset.prod_mul_distrib]

theorem tensor_sum (A : ι→Bool→Matrix Bool Bool R) :
    tensor (fun i=>∑b,A i b)=∑ε : ι→Bool,tensor (fun i=>A i (ε i)) := by
  ext z w
  simp only [tensor,Matrix.sum_apply]
  exact Fintype.prod_sum (fun i b=>A i b (z i) (w i))

def traceless (a u : R) : Matrix Bool Bool R :=
  fun i j=>if i=j then if i then -a else a else u

theorem traceless_square (a u : R) :
    traceless a u*traceless a u=(a^2+u^2) • (1 : Matrix Bool Bool R) := by
  ext i j
  cases i <;> cases j <;> simp [traceless,Matrix.mul_apply] <;> ring

def block (c a u : R) : Matrix Bool Bool R :=c • (1 : Matrix Bool Bool R)+traceless a u

def branch (c r : R) (ε : Bool) : R:=if ε then c-r else c+r

def projector (h q : R) (H : Matrix Bool Bool R) (ε : Bool) : Matrix Bool Bool R:=
  if ε then BooleanSpectralProjectors.minusProjector h q H else
    BooleanSpectralProjectors.plusProjector h q H

theorem block_power (c a u h q r : R) (hh:h+h=1) (hq:r*q=1)
    (hr:r^2=a^2+u^2) (n : ℕ) :
    (block c a u)^n=∑ε : Bool,(branch c r ε)^n • projector h q (traceless a u) ε := by
  simpa only [block,Fintype.sum_bool,branch,projector,Bool.false_eq_true,↓reduceIte,add_comm] using
    BooleanSpectralProjectors.power_decomposition h q r c (traceless a u) hh hq
      (by rw [traceless_square,hr]) n

def eigenvalue (c r : ι→R) (ε : ι→Bool) : R:=∏i,branch (c i) (r i) (ε i)

def eigenprojector (a u h q : ι→R) (ε : ι→Bool) : Matrix (ι→Bool) (ι→Bool) R:=
  tensor (fun i=>projector (h i) (q i) (traceless (a i) (u i)) (ε i))

/-- The actual power of the tensor matrix has the required finite moment form. -/
theorem tensor_power_expansion (c a u h q r : ι→R)
    (hh:∀i,h i+h i=1) (hq:∀i,r i*q i=1) (hr:∀i,r i^2=a i^2+u i^2) (n : ℕ) :
    (tensor (fun i=>block (c i) (a i) (u i)))^n=
      ∑ε : ι→Bool,(eigenvalue c r ε)^n • eigenprojector a u h q ε := by
  rw [tensor_pow]
  have hp : (fun i=>(block (c i) (a i) (u i))^n)=
      fun i=>∑ε : Bool,(branch (c i) (r i) ε)^n • projector (h i) (q i) (traceless (a i) (u i)) ε := by
    funext i
    exact block_power _ _ _ _ _ _ (hh i) (hq i) (hr i) n
  rw [hp]
  rw [tensor_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [tensor_scalar]
  simp only [eigenvalue,eigenprojector,Finset.prod_pow]

/-- Summing the projectors gives the literal identity tensor, including dimension zero. -/
theorem sum_eigenprojector (a u h q : ι→R) (hh:∀i,h i+h i=1) :
    (∑ε : ι→Bool,eigenprojector a u h q ε)=1 := by
  unfold eigenprojector
  rw [←tensor_sum]
  have hp : (fun i=>∑ε : Bool,projector (h i) (q i) (traceless (a i) (u i)) ε)=
      fun _=>(1 : Matrix Bool Bool R) := by
    funext i
    simpa only [Fintype.sum_bool,projector,Bool.false_eq_true,↓reduceIte,add_comm] using
      BooleanSpectralProjectors.projectors_sum (h i) (q i) (traceless (a i) (u i)) (hh i)
  rw [hp,tensor_one]

/-- Retaining a subset of coordinates changes only the scalar branch products;
the same projector family works for the whole tensor. -/
theorem retained_expansion (c a u h q r : ι→R) (S : Finset ι)
    (hh:∀i,h i+h i=1) (hq:∀i,r i*q i=1) (hr:∀i,r i^2=a i^2+u i^2) :
    tensor (fun i=>if i∈S then block (c i) (a i) (u i) else 1)=
      ∑ε : ι→Bool,(∏i,if i∈S then branch (c i) (r i) (ε i) else 1) •
        eigenprojector a u h q ε := by
  have hp : (fun i=>if i∈S then block (c i) (a i) (u i) else 1)=
      fun i=>∑ε : Bool,(if i∈S then branch (c i) (r i) ε else 1) •
        projector (h i) (q i) (traceless (a i) (u i)) ε := by
    funext i
    by_cases hi:i∈S
    · simpa only [hi,↓reduceIte,pow_one] using block_power _ _ _ _ _ _ (hh i) (hq i) (hr i) 1
    · simp only [hi,↓reduceIte,one_smul,Fintype.sum_bool,projector,Bool.false_eq_true]
      simpa only [↓reduceIte,add_comm] using
        (BooleanSpectralProjectors.projectors_sum (h i) (q i) (traceless (a i) (u i)) (hh i)).symm
  rw [hp,tensor_sum]
  apply Finset.sum_congr rfl
  intro ε _
  exact tensor_scalar _ _

end PlanarHom.BooleanTensorSpectral

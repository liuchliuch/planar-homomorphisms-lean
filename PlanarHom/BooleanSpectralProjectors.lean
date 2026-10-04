import PlanarHom.BooleanFieldTowerAlgebra
import PlanarHom.BooleanPDNormalization
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-! Explicit two-branch projectors over any commutative coefficient ring.
Only an inverse for the chosen nonzero radical and a half are used. This
includes the squarefree radical algebra even when it has zero divisors. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanSpectralProjectors
variable {R V : Type} [CommRing R] [Fintype V] [DecidableEq V]

def plusProjector (h q : R) (H : Matrix V V R) : Matrix V V R:=h • (1+q • H)
def minusProjector (h q : R) (H : Matrix V V R) : Matrix V V R:=h • (1-q • H)

theorem projectors_sum (h q : R) (H : Matrix V V R) (hh : h+h=1) :
    plusProjector h q H+minusProjector h q H=1 := by
  rw [plusProjector,minusProjector,←smul_add]
  have he : (1+q • H)+(1-q • H)=(1 : Matrix V V R)+1 := by abel
  rw [he,smul_add,←add_smul,hh,one_smul]

theorem plus_eigen (h q r c : R) (H : Matrix V V R) (hrq : r*q=1)
    (hH : H*H=r^2 • (1 : Matrix V V R)) :
    (c • (1 : Matrix V V R)+H)*plusProjector h q H=(c+r) • plusProjector h q H := by
  have hqr : q*r^2=r := by calc
    _=r*(r*q) := by ring
    _=r := by rw [hrq,mul_one]
  simp only [plusProjector,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,
    one_mul,mul_one,hH,smul_smul,hqr]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  linear_combination h * (1 : Matrix V V R) i j * hqr - h * H i j * hrq

theorem minus_eigen (h q r c : R) (H : Matrix V V R) (hrq : r*q=1)
    (hH : H*H=r^2 • (1 : Matrix V V R)) :
    (c • (1 : Matrix V V R)+H)*minusProjector h q H=(c-r) • minusProjector h q H := by
  have hrq' : (-r)*(-q)=1 := by simpa using hrq
  have hH' : H*H=(-r)^2 • (1 : Matrix V V R) := by simpa using hH
  simpa [plusProjector,minusProjector,neg_smul,sub_eq_add_neg] using plus_eigen h (-q) (-r) c H hrq' hH'

theorem power_decomposition (h q r c : R) (H : Matrix V V R) (hh : h+h=1)
    (hrq : r*q=1) (hH : H*H=r^2 • (1 : Matrix V V R)) (n : ℕ) :
    (c • (1 : Matrix V V R)+H)^n=
      (c+r)^n • plusProjector h q H+(c-r)^n • minusProjector h q H := by
  induction n with
  | zero=>simpa using (projectors_sum h q H hh).symm
  | succ n ih=>
    rw [pow_succ',ih,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,
      plus_eigen h q r c H hrq hH,minus_eigen h q r c H hrq hH,smul_smul,smul_smul]
    simp only [pow_succ,mul_comm]

end PlanarHom.BooleanSpectralProjectors

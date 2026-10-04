import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.BigOperators.Fin

/-! # A fixed cyclic matrix lift for algebraic power roots

If `A` has eigenvalue `r^n`, its cyclic `n`-block lift has eigenvalue `r`.
This construction uses only matrix entries, zeros and ones. In particular it
does not assume a factorization, root-finding, or eigenvector algorithm.
-/

noncomputable section
namespace PlanarHom.PowerRootLiftMatrix
open scoped BigOperators
open Matrix

variable {R : Type*} [CommRing R] {J : Type*} [Fintype J] [DecidableEq J]

def lift (n : ℕ) (A : Matrix J J R) : Matrix (Fin n × J) (Fin n × J) R :=
  fun i j => if h : i.1.val + 1 < n then
    if j.1 = ⟨i.1.val + 1, h⟩ then if j.2 = i.2 then 1 else 0 else 0
  else if j.1.val = 0 then A i.2 j.2 else 0

def eigenvector (n : ℕ) (r : R) (v : J → R) : (Fin n × J) → R :=
  fun i => r ^ i.1.val * v i.2

theorem lift_mulVec (n : ℕ) (A : Matrix J J R) (v : J → R) (i : Fin n × J) :
    (lift n A *ᵥ eigenvector n r v) i =
      if h : i.1.val + 1 < n then r^(i.1.val+1) * v i.2
      else (A *ᵥ v) i.2 := by
  classical
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, lift, eigenvector]
  split_ifs with h
  · simp [h]
  · have hn : 0 < n := Nat.zero_lt_of_lt i.1.isLt
    let z : Fin n := ⟨0, hn⟩
    have hz (j : Fin n) : j.val = 0 ↔ j = z := by simp [z, Fin.ext_iff]
    simp [h, hz, z]

theorem lift_eigen (n : ℕ) (A : Matrix J J R) (r : R) (v : J → R)
    (hv : A *ᵥ v = (r^n) • v) :
    lift n A *ᵥ eigenvector n r v = r • eigenvector n r v := by
  funext i
  rw [lift_mulVec]
  split_ifs with h
  · simp [eigenvector, pow_succ, mul_assoc, mul_comm, mul_left_comm]
  · have he : n = i.1.val + 1 := by omega
    rw [hv]
    simp only [eigenvector, Pi.smul_apply, smul_eq_mul]
    rw [show r^n = r^(i.1.val+1) from congrArg (fun k => r^k) he, pow_succ]
    ring

theorem eigenvector_ne_zero (n : ℕ) (hn : 0 < n) (r : R) (v : J → R)
    (hv : v ≠ 0) : eigenvector n r v ≠ 0 := by
  intro h
  apply hv
  funext j
  have he := congrFun h (⟨0, hn⟩, j)
  simpa [eigenvector] using he

theorem lift_map {S : Type*} [CommRing S] (f : R →+* S)
    (n : ℕ) (A : Matrix J J R) :
    (lift n A).map f = lift n (A.map f) := by
  ext i j
  simp only [Matrix.map_apply, lift]
  split_ifs <;> simp

theorem charpoly_eval_zero_of_eigen {K : Type*} [Field K]
    (A : Matrix J J K) (r : K) (v : J → K)
    (hv : v ≠ 0) (he : A *ᵥ v = r • v) : A.charpoly.eval r = 0 := by
  rw [Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, he]
  funext j
  simp [Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.smul_apply]

end PlanarHom.PowerRootLiftMatrix

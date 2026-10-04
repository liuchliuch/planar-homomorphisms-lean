import PlanarHom.OccurrencePfaffianShear
import Mathlib.LinearAlgebra.Determinant

/-! NEW: a variable-order determinant as a calibrated literal block Pfaffian.
The calibration is the same block matrix for the identity and is proved to be
a sign. No determinant or Pfaffian identity is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BlockPfaffian
open MultiGraph
attribute [-simp] Fin.natAdd_eq_addNat
variable {R : Type*} [CommRing R] {n : ℕ}

def block (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+n)) (Fin (n+n)) R :=
  Fin.addCases (fun i => Fin.addCases (fun _ => 0) (A i))
    (fun j => Fin.addCases (fun i => -A i j) (fun _ => 0))

@[simp] theorem block_ll (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    block A (i.castAdd n) (j.castAdd n) = 0 := by simp only [block, Fin.addCases_left, Fin.addCases_right]
@[simp] theorem block_lr (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    block A (i.castAdd n) (Fin.natAdd n j) = A i j := by simp only [block, Fin.addCases_left, Fin.addCases_right]
@[simp] theorem block_rl (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    block A (Fin.natAdd n i) (j.castAdd n) = -A j i := by simp only [block, Fin.addCases_left, Fin.addCases_right]
@[simp] theorem block_rr (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    block A (Fin.natAdd n i) (Fin.natAdd n j) = 0 := by simp only [block, Fin.addCases_left, Fin.addCases_right]

theorem block_skew (A : Matrix (Fin n) (Fin n) R) (u v : Fin (n+n)) :
    block A v u = -block A u v := by
  induction u using Fin.addCases <;> induction v using Fin.addCases <;> simp
theorem block_diag (A : Matrix (Fin n) (Fin n) R) (u : Fin (n+n)) :
    block A u u = 0 := by induction u using Fin.addCases <;> simp

@[simp] theorem right_ne_left (i j : Fin n) : Fin.natAdd n i ≠ Fin.castAdd n j := by
  intro h
  have hh := congrArg Fin.val h
  change n + i.val = j.val at hh
  omega
@[simp] theorem left_ne_right (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j :=
  (right_ne_left j i).symm

theorem block_update_combination [DecidableEq (Fin n)] (A : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (x y : Fin n → R) (a b : R) :
    block (Function.update A i (a • x + b • y)) =
      vertexCombination (i.castAdd n) a b (block (Function.update A i x))
        (block (Function.update A i y)) := by
  ext u v
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    simp only [block_ll, block_lr, block_rl, block_rr, vertexCombination]
  all_goals
    split_ifs <;> simp_all [Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals ring

theorem block_update_away [DecidableEq (Fin n)] (A : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (x y : Fin n → R) (u v : Fin (n+n))
    (hu : u ≠ i.castAdd n) (hv : v ≠ i.castAdd n) :
    block (Function.update A i x) u v = block (Function.update A i y) u v := by
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    simp_all [Function.update_apply]

def rowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R where
  toFun A := pairingPfaffian (block A)
  map_update_add' A i x y := by
    classical
    have h := supportedPfaffian_vertexCombination (Finset.univ : Finset (Fin (n+n)))
      (i := i.castAdd n) (by simp) (1:R) 1
      (block (Function.update A i x)) (block (Function.update A i y))
      (fun u _ v _ hu hv => block_update_away A i x y u v hu hv)
    rw [← block_update_combination, supportedPfaffian_univ,
      supportedPfaffian_univ, supportedPfaffian_univ] at h
    simpa using h
  map_update_smul' A i a x := by
    classical
    have h := supportedPfaffian_vertexCombination (Finset.univ : Finset (Fin (n+n)))
      (i := i.castAdd n) (by simp) a (0:R)
      (block (Function.update A i x)) (block (Function.update A i x))
      (fun _ _ _ _ _ _ => rfl)
    rw [← block_update_combination, supportedPfaffian_univ,
      supportedPfaffian_univ] at h
    simpa [smul_eq_mul] using h
  map_eq_zero_of_eq' A i j hij hne := by
    rw [← supportedPfaffian_univ]
    apply supportedPfaffian_eq_zero_of_equal_rows _ _ (i.castAdd n) (j.castAdd n)
      (by simp) (by simp) (by simpa using hne) (block_skew A) (block_diag A)
    intro v
    induction v using Fin.addCases <;> simp [hij]

theorem pairingPfaffian_block (A : Matrix (Fin n) (Fin n) R) :
    pairingPfaffian (block A) = pairingPfaffian (block (1 : Matrix (Fin n) (Fin n) R)) * A.det := by
  have h := congrArg (fun f : (Fin n → R) [⋀^Fin n]→ₗ[R] R => f A)
    ((rowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R).eq_smul_basis_det (Pi.basisFun R (Fin n)))
  have he : (Pi.basisFun R (Fin n) : Fin n → (Fin n → R)) = (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  change rowAlternating A = rowAlternating (Pi.basisFun R (Fin n)) *
    (Pi.basisFun R (Fin n)).det A at h
  rw [he, Pi.basisFun_det_apply] at h
  exact h

attribute [simp] Fin.natAdd_eq_addNat

end PlanarHom.BlockPfaffian

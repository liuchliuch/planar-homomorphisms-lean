import PlanarHom.PositiveUnaryRationalPowers
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-! Positive diagonal rational powers preserve off-diagonal zeros even at
exponent zero. The scalar relation is proved for every real exponent. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open ProductCompatibility
variable {I : Type}

def supportPower (A : I → ℝ) (r : ℝ) : I → ℝ :=
  fun i=>if A i=0 then 0 else (A i)^r

theorem supportPower_product (A : I → ℝ) (hA : ∀ i,A i≠0→0<A i) (r : ℝ)
    (xs : List I) (hnz : ∀ i∈xs,A i≠0) :
    (xs.map (supportPower A r)).prod=((xs.map A).prod)^r := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := hnz i (by simp)
    have ht : ∀ j∈xs,A j≠0 := fun j hj=>hnz j (by simp [hj])
    have hp : 0≤(xs.map A).prod := List.prod_nonneg (by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      exact (hA j (ht j hj)).le)
    simp only [List.map_cons,List.prod_cons,supportPower,if_neg hi]
    rw [ih ht,Real.mul_rpow (hA i hi).le hp]

theorem supportPower_compatible (A : I → ℝ) (hA : ∀ i,A i≠0→0<A i) (r : ℝ) :
    Compatible A (supportPower A r) := by
  intro xs ys _ hx hy h
  rw [supportPower_product A hA r xs hx,supportPower_product A hA r ys hy,h]

variable {q : ℕ}
def diagonalPower (w : Fin q → ℝ) (r : ℚ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.diagonal (fun i=>w i^(r:ℝ))

theorem diagonal_inverse_power (w : Fin q → ℝ) (hw : ∀ i,0<w i) (r : ℚ) :
    (fun p : Fin q × Fin q=>diagonalPower w r p.1 p.2) =
      supportPower (fun p : Fin q × Fin q=>Matrix.diagonal (fun i=>(w i)⁻¹) p.1 p.2) (-(r:ℝ)) := by
  funext p
  by_cases h : p.1=p.2
  · simp only [diagonalPower,Matrix.diagonal_apply,supportPower,if_pos h]
    rw [if_neg (inv_ne_zero (ne_of_gt (hw p.1))),Real.inv_rpow (hw p.1).le,Real.rpow_neg (hw p.1).le,inv_inv]
  · simp [diagonalPower,Matrix.diagonal_apply,supportPower,h]

theorem diagonalPower_compatible (w : Fin q → ℝ) (hw : ∀ i,0<w i) (r : ℚ) :
    Compatible (fun p : Fin q × Fin q=>Matrix.diagonal (fun i=>(w i)⁻¹) p.1 p.2)
      (fun p=>diagonalPower w r p.1 p.2) := by
  rw [diagonal_inverse_power w hw r]
  apply supportPower_compatible
  intro p hp
  by_cases h : p.1=p.2
  · simpa [Matrix.diagonal_apply,h] using inv_pos.mpr (hw p.1)
  · simp [Matrix.diagonal_apply,h] at hp

theorem diagonalPower_zero (w : Fin q → ℝ) (hw : ∀ i,0<w i) (r : ℚ)
    (i j : Fin q) (hz : Matrix.diagonal (fun i=>(w i)⁻¹) i j=0) :
    diagonalPower w r i j=0 := by
  have hne : i≠j := by
    intro h
    subst j
    exact (inv_ne_zero (ne_of_gt (hw i))) (by simpa using hz)
  simp [diagonalPower,Matrix.diagonal_apply,hne]

theorem diagonalPower_algebraic (w : Fin q → ℝ) (hw : ∀ i,0<w i)
    (ha : ∀ i,IsAlgebraic ℚ (w i)) (r : ℚ) : ∀ i j,IsAlgebraic ℚ (diagonalPower w r i j) := by
  intro i j
  by_cases h : i=j
  · subst j
    simpa [diagonalPower] using PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat (hw i) (ha i) r
  · simp only [diagonalPower,Matrix.diagonal_apply_ne _ h]
    exact isAlgebraic_zero

end PlanarHom.PositiveWeightRemoval

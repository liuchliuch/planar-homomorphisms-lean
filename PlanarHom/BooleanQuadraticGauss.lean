import PlanarHom.Boolean
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod

/-! NEW reconstruction: exact two-bit quadratic elimination identities.
These are finite character sums, without a normal-form or solver premise. -/
namespace PlanarHom.BooleanQuadraticGauss
open scoped BigOperators
variable {K : Type*} [CommRing K]

def sign (b : Bool) : K := if b then -1 else 1

@[simp] theorem sign_false : sign (K:=K) false=1 := rfl
@[simp] theorem sign_true : sign (K:=K) true = -1 := rfl

theorem sign_xor (a b : Bool) : sign (K:=K) (xor a b)=sign a*sign b := by
  cases a <;> cases b <;> simp [sign]

theorem pair_sum (a b c : Bool) :
    (∑ x : Bool, ∑ y : Bool,
      sign (K:=K) (xor c (xor (x && y) (xor (a && x) (b && y))))) =
      2 * sign (xor c (a && b)) := by
  cases a <;> cases b <;> cases c <;>
    simp [Fintype.sum_bool,sign] <;> ring

theorem singleton_sum (a c : Bool) :
    (∑ x : Bool, sign (K:=K) (xor c (a && x))) =
      if a then 0 else 2*sign c := by
  cases a <;> cases c <;> simp [Fintype.sum_bool,sign] <;> ring

/-- A literal two-coordinate split of the finite assignment space. -/
def splitPair {V B : Type*} [DecidableEq V] (i j : V) (hij : j ≠ i) :
    (V → B) ≃ B × B × ({k : V // k ≠ i ∧ k ≠ j} → B) where
  toFun x := (x i,x j,fun k=>x k.val)
  invFun p k := if hi : k=i then p.1 else if hj : k=j then p.2.1 else p.2.2 ⟨k,hi,hj⟩
  left_inv x := by funext k; by_cases hi:k=i <;> by_cases hj:k=j <;> simp_all
  right_inv p := by
    rcases p with ⟨x,y,z⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp [hij]
      · funext k
        simp [k.property.1,k.property.2]

/-- Eliminate an actual interacting pair after exposing its two affine rows.
The remaining variables retain their literal labels. -/
theorem sum_split_pair {V : Type*} [Fintype V] [DecidableEq V]
    (i j : V) (hij : j ≠ i)
    (a b c : ({k : V // k ≠ i ∧ k ≠ j} → Bool) → Bool) :
    (∑ x : V → Bool, sign (K:=K)
      (xor (c (fun k=>x k.val))
        (xor (x i && x j)
          (xor (a (fun k=>x k.val) && x i) (b (fun k=>x k.val) && x j))))) =
    2 * ∑ z, sign (xor (c z) (a z && b z)) := by
  classical
  rw [← (splitPair (B:=Bool) i j hij).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [splitPair,Equiv.coe_fn_symm_mk,dif_pos rfl,dif_neg hij]
  have hrest (x y : Bool) (z : {k : V // k ≠ i ∧ k ≠ j} → Bool) :
      (fun k : {k : V // k ≠ i ∧ k ≠ j} =>
        if hi : k.val=i then x else if hj : k.val=j then y else z ⟨k.val,hi,hj⟩) = z := by
    funext k
    simp [k.property.1,k.property.2]
  simp only [hrest,dite_true]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [pair_sum]
  exact (Finset.mul_sum _ _ _).symm
end PlanarHom.BooleanQuadraticGauss

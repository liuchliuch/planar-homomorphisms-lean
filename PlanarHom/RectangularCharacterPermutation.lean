import PlanarHom.RectangularRowConvolution
import PlanarHom.RectangularSignedPermutation
import PlanarHom.RectangularDegreeIndexSums

/-! NEW full character action of the genuine signed coordinate permutation. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

def permuteIndex (p:Fin d≃Fin d) (S:Cube d):Cube d:=fun j=>S (p.symm j)

def permutationRow (p:Fin d≃Fin d) (flip:Fin d→Bool) (S T:Cube d):ℝ:=
  if T=permuteIndex p S then character S flip else 0

theorem permuteIndex_injective (p:Fin d≃Fin d):Function.Injective (permuteIndex p):=by
  intro S T h
  funext i
  have hi:=congrFun h (p i)
  simpa only [permuteIndex,Equiv.symm_apply_apply] using hi

@[simp] theorem permuteIndex_zero (p:Fin d≃Fin d):permuteIndex p (fun _=>false)=(fun _=>false):=rfl
@[simp] theorem permuteIndex_xor (p:Fin d≃Fin d) (S T:Cube d):
    permuteIndex p (xor S T)=xor (permuteIndex p S) (permuteIndex p T):=rfl

theorem permuteIndex_degree (p:Fin d≃Fin d) (S:Cube d):Boolean.degree (permuteIndex p S)=Boolean.degree S:=by
  unfold Boolean.degree permuteIndex
  exact Equiv.sum_comp p.symm (fun i:Fin d=>if S i then (1:ℕ) else 0)

theorem permuteIndex_singleton (p:Fin d≃Fin d) (i:Fin d):permuteIndex p (unitBit i)=unitBit (p i):=by
  funext j
  simp [permuteIndex,unitBit,Equiv.symm_apply_eq]

theorem character_singleton (i:Fin d) (flip:Cube d):character (unitBit i) flip=signValue (flip i):=by
  rw [character_symm,character_unitBit]
  rfl

theorem permutationRow_singleton (p:Fin d≃Fin d) (flip:Fin d→Bool) (i j:Fin d):
    permutationRow p flip (unitBit i) (unitBit j)=if j=p i then signValue (flip i) else 0:=by
  simp only [permutationRow,permuteIndex_singleton,unitBit_injective.eq_iff,character_singleton]

theorem permutationRow_norm (p:Fin d≃Fin d) (flip:Fin d→Bool) (S:Cube d):
    (∑T:Cube d,permutationRow p flip S T^2)=1:=by
  simp only [permutationRow,ite_pow,zero_pow (by decide:2≠0)]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]
  simpa only [pow_two] using character_mul_self S flip

theorem xor_eq_iff (T I J:Cube d):xor T I=J↔T=xor I J:=by
  constructor
  · intro h
    funext i
    have hi:=congrFun h i
    have hb (x y z:Bool):Bool.xor x y=z→x=Bool.xor y z:=by cases x <;> cases y <;> cases z <;> decide
    exact hb _ _ _ hi
  · intro h
    subst T
    funext i
    simp [Boolean.xor,Bool.xor_comm,Bool.xor_left_comm]

theorem permutationRow_convolution (p:Fin d≃Fin d) (flip:Fin d→Bool) (I J T:Cube d):
    rowConvolution (permutationRow p flip I) (permutationRow p flip J) T=
      permutationRow p flip (xor I J) T:=by
  simp only [rowConvolution,permutationRow,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]
  simp only [xor_eq_iff,←permuteIndex_xor]
  split_ifs <;> simp only [←character_mul,mul_zero]

theorem permutationRow_degree (p:Fin d≃Fin d) (flip:Fin d→Bool) (S T:Cube d)
    (h:Boolean.degree S≠Boolean.degree T):permutationRow p flip S T=0:=by
  apply if_neg
  intro he
  subst T
  exact h (permuteIndex_degree p S).symm

theorem signedColor_character (p:Fin d≃Fin d) (flip:Fin d→Bool) (S y:Cube d):
    character S (signedColorEquiv p flip y)=character S flip*character (permuteIndex p S) y:=by
  have hx:signedColorEquiv p flip y=xor flip (fun i=>y (p i)):=rfl
  rw [hx,character_xor]
  congr 1
  unfold character permuteIndex
  symm
  apply Fintype.prod_equiv p.symm
  intro j
  simp only [Equiv.apply_symm_apply]

end PlanarHom.RectangularWalshConvolution

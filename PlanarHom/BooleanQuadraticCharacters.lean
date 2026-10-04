import PlanarHom.BooleanQuadraticAlgebra

/-! NEW exact character and arbitrary-coordinate elimination over F₂. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators
variable {K : Type*} [CommRing K]

def character (z : F₂) : K := if z=0 then 1 else -1
@[simp] theorem character_zero : character (K:=K) 0=1 := by simp [character]
@[simp] theorem character_one : character (K:=K) 1= -1 := by simp [character]

theorem character_bit (b : Bool) : character (K:=K) (bit b)=BooleanQuadraticGauss.sign b := by
  cases b <;> simp [BooleanQuadraticGauss.sign]

def bitEquiv : Bool ≃ F₂ where
  toFun := bit
  invFun x := decide (x=1)
  left_inv b := by cases b <;> decide
  right_inv x := by fin_cases x <;> decide

theorem character_add (x y : F₂) :
    character (K:=K) (x+y)=character x*character y := by
  obtain ⟨a,rfl⟩:=bitEquiv.surjective x
  obtain ⟨b,rfl⟩:=bitEquiv.surjective y
  change character (bit a+bit b)=character (bit a)*character (bit b)
  rw [←bit_xor,character_bit,character_bit,character_bit,BooleanQuadraticGauss.sign_xor]

theorem pair_character_sum (a b c : F₂) :
    (∑x:F₂,∑y:F₂,character (K:=K) (c+x*y+a*x+b*y)) =
      2*character (c+a*b) := by
  obtain ⟨a,rfl⟩:=bitEquiv.surjective a
  obtain ⟨b,rfl⟩:=bitEquiv.surjective b
  obtain ⟨c,rfl⟩:=bitEquiv.surjective c
  rw [←bitEquiv.sum_comp]
  simp_rw [←bitEquiv.sum_comp]
  change (∑x:Bool,∑y:Bool,character (K:=K)
    (bit c+bit x*bit y+bit a*bit x+bit b*bit y))=2*character (bit c+bit a*bit b)
  simp_rw [←bit_and,←bit_xor,character_bit,Bool.xor_assoc]
  exact BooleanQuadraticGauss.pair_sum a b c

theorem singleton_character_sum (a c : F₂) :
    (∑x:F₂,character (K:=K) (c+a*x)) =
      if a=0 then 2*character c else 0 := by
  obtain ⟨a,rfl⟩:=bitEquiv.surjective a
  obtain ⟨c,rfl⟩:=bitEquiv.surjective c
  rw [←bitEquiv.sum_comp]
  change (∑x:Bool,character (K:=K) (bit c+bit a*bit x))=
    if bit a=0 then 2*character (bit c) else 0
  simp_rw [←bit_and,←bit_xor,character_bit]
  rw [BooleanQuadraticGauss.singleton_sum]
  cases a <;> simp [bit]

/-- Eliminating an interacting pair multiplies the full ambient character sum
by two. Removed coordinates remain free in the residual sum. -/
theorem pair_elimination {V : Type*} [Fintype V] [DecidableEq V]
    (i j : V) (hij : j≠i)
    (a b c : ({k:V // k≠i ∧ k≠j}→F₂)→F₂) :
    2*(∑x:V→F₂,character (K:=K)
      (c (fun k=>x k.val)+x i*x j+a (fun k=>x k.val)*x i+b (fun k=>x k.val)*x j)) =
    ∑x:V→F₂,character (c (fun k=>x k.val)+a (fun k=>x k.val)*b (fun k=>x k.val)) := by
  classical
  let e:=BooleanQuadraticGauss.splitPair (B:=F₂) i j hij
  rw [←e.symm.sum_comp,←e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hrest (x y:F₂) (z:{k:V // k≠i ∧ k≠j}→F₂) :
      (fun k:{k:V // k≠i ∧ k≠j}=>e.symm (x,y,z) k.val)=z := by
    funext k
    simp [e,BooleanQuadraticGauss.splitPair,k.property.1,k.property.2]
  have hi (x y:F₂) (z:{k:V // k≠i ∧ k≠j}→F₂) : e.symm (x,y,z) i=x := by
    simp [e,BooleanQuadraticGauss.splitPair]
  have hj (x y:F₂) (z:{k:V // k≠i ∧ k≠j}→F₂) : e.symm (x,y,z) j=y := by
    simp [e,BooleanQuadraticGauss.splitPair,hij]
  simp only [hrest,hi,hj]
  conv_lhs => arg 2; arg 2; ext x; rw [Finset.sum_comm]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  simp_rw [pair_character_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    show Fintype.card F₂=2 from Fintype.card_congr bitEquiv.symm,nsmul_eq_mul]
  rw [←Finset.mul_sum]
  ring

/-- The singleton step either leaves the ambient sum unchanged or annihilates
it; this includes loops, whose diagonal coefficient is linear over F₂. -/
theorem singleton_elimination {V : Type*} [Fintype V] [DecidableEq V]
    (i : V) (a : F₂) (c : ({k:V // k≠i}→F₂)→F₂) :
    (∑x:V→F₂,character (K:=K) (c (fun k=>x k.val)+a*x i)) =
      if a=0 then (∑x:V→F₂,character (c (fun k=>x k.val))) else 0 := by
  classical
  let e:=Equiv.funSplitAt i F₂
  rw [←e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hrest (x:F₂) (z:{k:V // k≠i}→F₂) :
      (fun k:{k:V // k≠i}=>e.symm (x,z) k.val)=z := by
    funext k
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt,k.property]
  have hi (x:F₂) (z:{k:V // k≠i}→F₂) : e.symm (x,z) i=x := by
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
  simp only [hrest,hi]
  rw [Finset.sum_comm]
  simp_rw [singleton_character_sum]
  by_cases ha:a=0
  · simp only [ha,ite_true]
    rw [←e.symm.sum_comp]
    simp only [Fintype.sum_prod_type,hrest,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      show Fintype.card F₂=2 from Fintype.card_congr bitEquiv.symm,Nat.cast_ofNat]
    exact (Finset.mul_sum _ _ _).symm
  · simp [ha]

end PlanarHom.BooleanQuadratic

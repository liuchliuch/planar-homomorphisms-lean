import PlanarHom.BooleanTensorPartitionMoments
import PlanarHom.BooleanTowerSpectral

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom BooleanTensorSpectral

-- Projector arithmetic genuinely applies to a ring with zero divisors.
example : ((1,0) : ℚ×ℚ)*((0,1) : ℚ×ℚ)=0 := by ext <;> norm_num
example (n : ℕ) :
    (block ((2,3):ℚ×ℚ) (0,0) (1,2))^n=
      ∑ε : Bool,branch ((2,3):ℚ×ℚ) (1,2) ε ^n •
        projector (1/2,1/2) (1,1/2) (traceless (0,0) (1,2)) ε := by
  apply block_power <;> ext <;> norm_num

-- Zero tensor dimension is the singleton identity matrix, including power zero.
example (n : ℕ) :
    (tensor (fun i : Fin 0=> (Fin.elim0 i : Matrix Bool Bool ℚ)))^n=1 := by
  have h : tensor (fun i : Fin 0=> (Fin.elim0 i : Matrix Bool Bool ℚ))=1 := by
    ext z w
    have he:z=w:=Subsingleton.elim _ _
    subst w
    simp [tensor]
  rw [h,one_pow]

private def loopCode : Complexity.MixedCode:=⟨2,[(0,0,0),(0,0,0),(0,1,1)],[(0,0)]⟩
private theorem loop_valid : loopCode.Valid 2 1 := by simp [Complexity.MixedCode.Valid,loopCode]
private def c : Fin 1→ℚ:=fun _=>2
private def a : Fin 1→ℚ:=fun _=>0
private def u : Fin 1→ℚ:=fun _=>1
private def half : Fin 1→ℚ:=fun _=>1/2
private def one : Fin 1→ℚ:=fun _=>1
-- Repeated input loops, a signed unchanged matrix, signed unary, and signed background.
example (n:ℕ) :
    loopCode.evaluate loop_valid
      (BooleanTensorPartitionMoments.replace (fun _ _ _=>(-2:ℚ)) 0
        ((tensor (fun i=>block (c i) (a i) (u i)))^n))
      (fun _ z=>if z 0 then -3 else 0) (fun z=>if z 0 then -1 else 2)=
      ∑z : (Fin loopCode.vertices→(Fin 1→Bool)) ×
        (Fin (loopCode.markedCount 0)→(Fin 1→Bool)),
        BooleanTensorPartitionMoments.rest loopCode loop_valid 0 (fun _ _ _=>(-2:ℚ))
          (fun _ z=>if z 0 then -3 else 0) (fun z=>if z 0 then -1 else 2) a u half one z *
          (∏e,eigenvalue c one (z.2 e))^n := by
  apply BooleanTensorPartitionMoments.evaluate_power <;> intro i <;> norm_num [c,a,u,half,one]

-- Square/dependent radicands have legitimate generator inverses without a field instance.
example : BooleanTowerSpectral.radical (fun _:ℕ=>(1:ℚ)) (0:Fin 2)*
    BooleanTowerSpectral.inverseRadical (fun _:ℕ=>(1:ℚ)) (0:Fin 2)=1 :=
  BooleanTowerSpectral.radical_mul_inverse _ _ (by norm_num)

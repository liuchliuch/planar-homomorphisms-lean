import PlanarHom.GadgetColorAutomorphisms

/-! NEW extension of an actual color permutation on one zero-separated
matrix block. Global gadget diagonal separation therefore restricts each block. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
variable {C D:Type}

 def Rigid (M:Matrix C C ℝ) : Prop :=
  ∀p:Equiv.Perm C,(∀i j,M (p i) (p j)=M i j)→∀i,p i=i

 theorem Separates.rigid [Fintype C] {M:Matrix C C ℝ} (h:Separates M) : Rigid M :=
  automorphism_fixed M h

 def fiberMap (b:C→D) (r:D) (p:Equiv.Perm {c // b c=r}) (c:C) : C :=
  if h:b c=r then (p ⟨c,h⟩).val else c

 theorem fiberMap_on (b:C→D) (r:D) (p:Equiv.Perm {c // b c=r}) (c:{c // b c=r}) :
    fiberMap b r p c.val=(p c).val := by simp only [fiberMap,c.property,dif_pos,Subtype.eta]

 theorem fiberMap_off (b:C→D) (r:D) (p:Equiv.Perm {c // b c=r}) (c:C) (hc:b c≠r) :
    fiberMap b r p c=c := by simp only [fiberMap,dif_neg hc]

 theorem fiberMap_inverse (b:C→D) (r:D) (p:Equiv.Perm {c // b c=r}) (c:C) :
    fiberMap b r p.symm (fiberMap b r p c)=c := by
  by_cases hc:b c=r
  · have hh:=fiberMap_on b r p ⟨c,hc⟩
    rw [hh,fiberMap_on]
    exact congrArg Subtype.val (p.symm_apply_apply ⟨c,hc⟩)
  · rw [fiberMap_off b r p c hc,fiberMap_off b r p.symm c hc]

 def fiberPerm (b:C→D) (r:D) (p:Equiv.Perm {c // b c=r}) : Equiv.Perm C where
  toFun:=fiberMap b r p
  invFun:=fiberMap b r p.symm
  left_inv:=fiberMap_inverse b r p
  right_inv:=fiberMap_inverse b r p.symm

 theorem fiberPerm_preserves (M:Matrix C C ℝ) (b:C→D) (r:D)
    (hz:∀i j,b i≠b j→M i j=0) (p:Equiv.Perm {c // b c=r})
    (hp:∀i j,M (p i).val (p j).val=M i.val j.val) :
    ∀i j,M (fiberPerm b r p i) (fiberPerm b r p j)=M i j := by
  intro i j
  change M (fiberMap b r p i) (fiberMap b r p j)=_
  by_cases hi:b i=r <;> by_cases hj:b j=r
  · rw [fiberMap_on b r p ⟨i,hi⟩,fiberMap_on b r p ⟨j,hj⟩]
    exact hp ⟨i,hi⟩ ⟨j,hj⟩
  · rw [fiberMap_on b r p ⟨i,hi⟩,fiberMap_off b r p j hj]
    rw [hz _ j (by simpa only [(p ⟨i,hi⟩).property] using (Ne.symm hj)),hz i j (by simpa only [hi] using (Ne.symm hj))]
  · rw [fiberMap_off b r p i hi,fiberMap_on b r p ⟨j,hj⟩]
    rw [hz i _ (by simpa only [(p ⟨j,hj⟩).property] using hi),hz i j (by simpa only [hj] using hi)]
  · rw [fiberMap_off b r p i hi,fiberMap_off b r p j hj]

 theorem Rigid.fiber {M:Matrix C C ℝ} (h:Rigid M) (b:C→D) (r:D)
    (hz:∀i j,b i≠b j→M i j=0) : Rigid (fun i j:{c // b c=r}=>M i.val j.val) := by
  intro p hp i
  apply Subtype.ext
  have he:=h (fiberPerm b r p) (fiberPerm_preserves M b r hz p hp) i.val
  change fiberMap b r p i.val=i.val at he
  simpa only [fiberMap_on] using he

end PlanarHom.GadgetDiagonalSeparation

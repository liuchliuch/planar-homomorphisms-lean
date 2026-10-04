import PlanarHom.ColorAutomorphismFibers
import PlanarHom.Structures

/-! NEW actual coordinate-flip automorphisms of every tensor block. A gadget
separating all color diagonals excludes even degenerate nonempty cube factors. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
open Boolean Structures
variable {C A:Type} {d:ℕ}

 def cubeTranslate (z:Cube d) : Equiv.Perm (Cube d) where
  toFun x:=Boolean.xor x z
  invFun x:=Boolean.xor x z
  left_inv x:=by funext r;dsimp only [Boolean.xor];cases x r <;> cases z r <;> rfl
  right_inv x:=by funext r;dsimp only [Boolean.xor];cases x r <;> cases z r <;> rfl

 def flipColor (e:C≃A×Cube d) (z:Cube d) : Equiv.Perm C :=
  e.trans ((Equiv.prodCongr (Equiv.refl A) (cubeTranslate z)).trans e.symm)

 theorem flipColor_chart (e:C≃A×Cube d) (z:Cube d) (i:C) :
    e (flipColor e z i)=((e i).1,Boolean.xor (e i).2 z) := by
  simp only [flipColor,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodCongr_apply,Equiv.refl_apply]
  rfl

 theorem flipColor_preserves (M:Matrix C C ℝ) (e:C≃A×Cube d) (F:A→A→ℝ) (ρ:Fin d→ℝ)
    (hM:∀i j,M i j=F (e i).1 (e j).1*tensor ρ (e i).2 (e j).2) (z:Cube d) :
    ∀i j,M (flipColor e z i) (flipColor e z j)=M i j := by
  intro i j
  simp only [hM,flipColor_chart,tensor_xor]

 theorem tensor_dimension_zero [Nonempty A] (M:Matrix C C ℝ) (h:Rigid M)
    (e:C≃A×Cube d) (F:A→A→ℝ) (ρ:Fin d→ℝ)
    (hM:∀i j,M i j=F (e i).1 (e j).1*tensor ρ (e i).2 (e j).2) : d=0 := by
  by_contra hd
  let r:Fin d:=⟨0,Nat.pos_of_ne_zero hd⟩
  let a:A:=Classical.choice inferInstance
  let c:C:=e.symm (a,fun _=>false)
  have hh:=h (flipColor e (unitBit r)) (flipColor_preserves M e F ρ hM (unitBit r)) c
  have he:=congrArg (fun i:C=>(e i).2 r) hh
  simp only [flipColor_chart,c,Equiv.apply_symm_apply,Boolean.xor,unitBit,decide_true,Bool.false_xor] at he
  contradiction

 def emptyCubeEquiv (A:Type) : A×Cube 0≃A where
  toFun:=Prod.fst
  invFun a:=(a,fun i=>i.elim0)
  left_inv p:=Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _:=rfl

 inductive BasicBlock (M:Matrix C C ℝ) : Prop
  | zero (e:C≃Unit) (hM:∀i j,M i j=0) : BasicBlock M
  | positive (k:ℕ) (hk:0<k) (a:Fin k→ℝ) (ha:∀i,0<a i) (e:C≃Fin k)
      (hM:∀i j,M i j=a (e i)*a (e j)) : BasicBlock M
  | bipartite (k l:ℕ) (hk:0<k) (hl:0<l) (a:Fin k→ℝ) (b:Fin l→ℝ)
      (ha:∀i,0<a i) (hb:∀j,0<b j) (e:C≃Fin k⊕Fin l)
      (hM:∀i j,M i j=bipartiteAmplitude a b (e i) (e j)) : BasicBlock M

 def BasicClass (M:Matrix C C ℝ) : Prop :=
  ∃t,∃block:C→Fin t,Function.Surjective block ∧
    (∀i j,block i≠block j→M i j=0) ∧
    ∀r,BasicBlock (fun i j:{c // block c=r}=>M i.val j.val)

 theorem allowedBlock_basic_of_rigid {M:Matrix C C ℝ} (h:AllowedBlock M) (hr:Rigid M) : BasicBlock M := by
  cases h with
  | zero e hM => exact .zero e hM
  | positive k d hk a ρ ha hρ e hM =>
    letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
    have hd:=tensor_dimension_zero M hr e (fun i j=>a i*a j) ρ hM
    subst d
    exact .positive k hk a ha (e.trans (emptyCubeEquiv _)) (by intro i j;simpa only [tensor_empty,mul_one] using hM i j)
  | bipartite k l d hk hl a b ρ ha hb hρ e hM =>
    letI : Nonempty (Fin k⊕Fin l):=⟨.inl ⟨0,hk⟩⟩
    have hd:=tensor_dimension_zero M hr e (bipartiteAmplitude a b) ρ hM
    subst d
    exact .bipartite k l hk hl a b ha hb (e.trans (emptyCubeEquiv _)) (by intro i j;simpa only [tensor_empty,mul_one] using hM i j)

 theorem BasicBlock.allowed {M:Matrix C C ℝ} (h:BasicBlock M) : AllowedBlock M := by
  cases h with
  | zero e hM => exact .zero e hM
  | positive k hk a ha e hM =>
    exact .positive k 0 hk a (fun i=>i.elim0) ha (fun i=>i.elim0)
      (e.trans (emptyCubeEquiv _).symm) (by intro i j;simpa only [tensor_empty,mul_one] using hM i j)
  | bipartite k l hk hl a b ha hb e hM =>
    exact .bipartite k l 0 hk hl a b (fun i=>i.elim0) ha hb (fun i=>i.elim0)
      (e.trans (emptyCubeEquiv _).symm) (by intro i j;simpa only [tensor_empty,mul_one] using hM i j)

 theorem BasicClass.nonnegativeClass {M:Matrix C C ℝ} (h:BasicClass M) : NonnegativeClass M := by
  obtain ⟨t,b,hb,hz,hf⟩:=h
  exact ⟨t,b,hb,hz,fun r=>(hf r).allowed⟩

 theorem basicClass_of_separates [Fintype C] {M:Matrix C C ℝ} (hsep:Separates M)
    (h:NonnegativeClass M) : BasicClass M := by
  obtain ⟨t,b,hb,hz,hf⟩:=h
  exact ⟨t,b,hb,hz,fun r=>allowedBlock_basic_of_rigid (hf r) (hsep.rigid.fiber b r hz)⟩

 theorem nonnegativeClass_iff_basic [Fintype C] {M:Matrix C C ℝ} (hsep:Separates M) :
    NonnegativeClass M ↔ BasicClass M := ⟨basicClass_of_separates hsep,BasicClass.nonnegativeClass⟩

end PlanarHom.GadgetDiagonalSeparation

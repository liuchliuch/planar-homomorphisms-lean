import PlanarHom.TensorColorAutomorphisms
import Mathlib.LinearAlgebra.Matrix.Rank

/-! NEW positive distinct-diagonal consequence of the literal structural
class. Coordinate-flip rigidity leaves a genuine positive rank-one matrix. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
open Structures
variable {C D:Type}

 theorem rigid_of_injective_diagonal (M:Matrix C C ℝ) (h:Function.Injective (fun i=>M i i)) : Rigid M := by
  intro p hp i
  exact h (hp i i)

 theorem basicClass_of_rigid {M:Matrix C C ℝ} (hr:Rigid M) (h:NonnegativeClass M) : BasicClass M := by
  obtain ⟨t,b,hb,hz,hf⟩:=h
  exact ⟨t,b,hb,hz,fun r=>allowedBlock_basic_of_rigid (hf r) (hr.fiber b r hz)⟩

 theorem BasicBlock.equiv {M:Matrix C C ℝ} (h:BasicBlock M) (e:D≃C) :
    BasicBlock (fun i j=>M (e i) (e j)) := by
  cases h with
  | zero c hz => exact .zero (e.trans c) (fun i j=>hz _ _)
  | positive k hk a ha c hm => exact .positive k hk a ha (e.trans c) (fun i j=>hm _ _)
  | bipartite k l hk hl a b ha hb c hm => exact .bipartite k l hk hl a b ha hb (e.trans c) (fun i j=>hm _ _)

 theorem basicBlock_of_positive [Nonempty C] (M:Matrix C C ℝ) (hp:∀i j,0<M i j) (h:BasicClass M) :
    BasicBlock M := by
  obtain ⟨t,b,hb,hz,hf⟩:=h
  let c:C:=Classical.choice inferInstance
  have hbc:∀i,b i=b c:=by
    intro i
    by_contra hi
    exact (hp i c).ne' (hz i c hi)
  let e:C≃{i // b i=b c}:={
    toFun:=fun i=>⟨i,hbc i⟩
    invFun:=Subtype.val
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (hf (b c)).equiv e

 theorem positive_basic_amplitude [Nonempty C] (M:Matrix C C ℝ) (hp:∀i j,0<M i j) (h:BasicBlock M) :
    ∃a:C→ℝ,(∀i,0<a i) ∧ ∀i j,M i j=a i*a j := by
  cases h with
  | zero e hz => exact ((hp (e.symm ()) (e.symm ())).ne' (hz _ _)).elim
  | positive k hk a ha e hm => exact ⟨fun i=>a (e i),fun i=>ha _,hm⟩
  | bipartite k l hk hl a b ha hb e hm =>
    let i:=e.symm (.inl ⟨0,hk⟩)
    have hz:M i i=0:=by simp only [hm,i,Equiv.apply_symm_apply,bipartiteAmplitude]
    exact ((hp i i).ne' hz).elim

 theorem nonnegativeClass_rank_le_one [Fintype C] [Nonempty C] (M:Matrix C C ℝ)
    (hp:∀i j,0<M i j) (hd:Function.Injective (fun i=>M i i)) (h:NonnegativeClass M) : M.rank≤1 := by
  obtain ⟨a,ha,hm⟩:=positive_basic_amplitude M hp
    (basicBlock_of_positive M hp (basicClass_of_rigid (rigid_of_injective_diagonal M hd) h))
  have he:M=Matrix.vecMulVec a a:=funext (fun i=>funext (fun j=>hm i j))
  rw [he]
  exact Matrix.rank_vecMulVec_le a a

end PlanarHom.GadgetDiagonalSeparation

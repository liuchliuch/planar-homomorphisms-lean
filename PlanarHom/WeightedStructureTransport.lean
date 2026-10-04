import PlanarHom.Structures
namespace PlanarHom.Structures
variable {C D : Type}
theorem AllowedWeightedBlock.equiv {M : Matrix C C ℝ} {w : C→ℝ}
    (h : AllowedWeightedBlock M w) (e : D≃C) :
    AllowedWeightedBlock (fun i j=>M (e i) (e j)) (fun i=>w (e i)) := by
  cases h with
  | zero c hM hw => exact .zero (e.trans c) (fun i j=>hM _ _) (fun i=>hw _)
  | positive k d hk a mass ρ ha hm hρ c hM hw =>
    exact .positive k d hk a mass ρ ha hm hρ (e.trans c) (fun i j=>hM _ _) (fun i=>hw _)
  | bipartite k l d hk hl a massX b massY ρ ha hb hmx hmy hρ c hM hw =>
    exact .bipartite k l d hk hl a massX b massY ρ ha hb hmx hmy hρ
      (e.trans c) (fun i j=>hM _ _) (fun i=>hw _)
theorem AllowedWeightedBlock.of_equiv {M : Matrix C C ℝ} {w : C→ℝ}
    (e : D≃C) (h : AllowedWeightedBlock (fun i j=>M (e i) (e j)) (fun i=>w (e i))) :
    AllowedWeightedBlock M w := by
  simpa only [Equiv.apply_symm_apply] using h.equiv e.symm
theorem WeightedClass.equiv {M : Matrix C C ℝ} {w : C→ℝ}
    (h : WeightedClass M w) (e : D≃C) :
    WeightedClass (fun i j=>M (e i) (e j)) (fun i=>w (e i)) := by
  obtain ⟨t,b,hb,hz,hf⟩ := h
  refine ⟨t,b∘e,hb.comp e.surjective,(fun i j hij=>hz _ _ hij),?_⟩
  intro r
  let er : {i // b (e i)=r}≃{j // b j=r} := {
    toFun:=fun i=>⟨e i.val,i.property⟩
    invFun:=fun j=>⟨e.symm j.val,by simpa only [Equiv.apply_symm_apply] using j.property⟩
    left_inv:=fun i=>Subtype.ext (e.symm_apply_apply i.val)
    right_inv:=fun j=>Subtype.ext (e.apply_symm_apply j.val) }
  exact (hf r).equiv er
theorem WeightedClass.of_equiv {M : Matrix C C ℝ} {w : C→ℝ}
    (e : D≃C) (h : WeightedClass (fun i j=>M (e i) (e j)) (fun i=>w (e i))) :
    WeightedClass M w := by
  simpa only [Equiv.apply_symm_apply] using h.equiv e.symm
end PlanarHom.Structures

import PlanarHom.BipartiteRankTwoEvaluationMachines
import PlanarHom.WeightedBlockFPClosure
import PlanarHom.BooleanTensorEasyAssembly

/-! NEW original-field source algorithm for bipartite rank-two Ising blocks.
Canonical anchor rescaling represents both amplitude vectors and every Ising
parameter in the original field. Unequal sides and independent original masses
are retained. Only primitive positive Ising FP is an external premise. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.BipartiteRankTwoTractability
open Complexity Complexity.MixedCode BooleanTensorEasyAssembly
variable {C : Type} [Fintype C] {dimension k l d : ℕ}

theorem source_weighted_ising_tensor_inFP_of_ising (hIsing : PositiveIsingFoundation)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀) (w : C → K₀)
    (i0 : Fin k) (j0 : Fin l) (e : C ≃ (Fin k ⊕ Fin l) × Boolean.Cube d)
    (a : Fin k → ℝ) (ha : ∀i,0<a i) (b : Fin l → ℝ) (hb : ∀j,0<b j)
    (ρ : Fin d → ℝ) (hρ : ∀r,0<ρ r) (μ : Fin k → ℝ) (ν : Fin l → ℝ)
    (hsource : Matrix.reindex e e (fun i j=>(M i j:ℝ)) =
      MultiGraph.tensorInteraction (matrix a b) (Boolean.tensor ρ))
    (hweight : ∀i,(w i:ℝ)=Sum.elim μ ν (e i).1) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).InFP := by
  let z : Boolean.Cube d := fun _=>false
  have he (p r : (Fin k ⊕ Fin l) × Boolean.Cube d) :
      (M (e.symm p) (e.symm r):ℝ)=matrix a b p.1 r.1 * Boolean.tensor ρ p.2 r.2 :=
    congrArg (fun A : Matrix _ _ ℝ=>A p r) hsource
  let anchor := M (e.symm (.inl i0,z)) (e.symm (.inr j0,z))
  have hanchor : (anchor:ℝ)=a i0*b j0 := by
    simpa only [anchor,he,matrix_inl_inr,Boolean.tensor_diag,mul_one]
  have hane : (anchor:ℝ)≠0 := by rw [hanchor]; exact (mul_pos (ha i0) (hb j0)).ne'
  let aK : Fin k → K₀ := fun i=>M (e.symm (.inl i,z)) (e.symm (.inr j0,z))
  let bK : Fin l → K₀ := fun j=>M (e.symm (.inl i0,z)) (e.symm (.inr j,z))/anchor
  let ρK : Fin d → K₀ := fun r=>M (e.symm (.inl i0,z))
    (e.symm (.inr j0,Boolean.unitBit r))/anchor
  let μK : Fin k → K₀ := fun i=>w (e.symm (.inl i,z))
  let νK : Fin l → K₀ := fun j=>w (e.symm (.inr j,z))
  have haK (i : Fin k) : (aK i:ℝ)=a i*b j0 := by
    simpa only [aK,he,matrix_inl_inr,Boolean.tensor_diag,mul_one]
  have hbK (j : Fin l) : (bK j:ℝ)=b j/b j0 := by
    change (M (e.symm (.inl i0,z)) (e.symm (.inr j,z)):ℝ)/(anchor:ℝ)=_
    rw [he,hanchor]
    simp only [matrix_inl_inr,Boolean.tensor_diag,mul_one]
    field_simp [(ha i0).ne',(hb j0).ne']
  have hrK (r : Fin d) : (ρK r:ℝ)=ρ r := by
    change (M (e.symm (.inl i0,z)) (e.symm (.inr j0,Boolean.unitBit r)):ℝ)/(anchor:ℝ)=_
    rw [he,hanchor]
    simp only [matrix_inl_inr,z,Boolean.tensor_unitBit]
    field_simp [(ha i0).ne',(hb j0).ne']
  have hpK (i : Fin k) (j : Fin l) : (aK i:ℝ)*(bK j:ℝ)=a i*b j := by
    rw [haK,hbK]
    field_simp [(hb j0).ne']
  have hμK (i : Fin k) : (μK i:ℝ)=μ i := by
    change (w (e.symm (.inl i,z)):ℝ)=_
    rw [hweight,e.apply_symm_apply]
    rfl
  have hνK (j : Fin l) : (νK j:ℝ)=ν j := by
    change (w (e.symm (.inr j,z)):ℝ)=_
    rw [hweight,e.apply_symm_apply]
    rfl
  let T : Matrix (Boolean.Cube d) (Boolean.Cube d) K₀ :=
    BooleanTensorSpectral.tensor (fun r=>isingMatrix (ρK r))
  have hT (i j : Boolean.Cube d) : (T i j:ℝ)=Boolean.tensor ρ i j := by
    simp [T,BooleanTensorSpectral.tensor,Boolean.tensor,isingMatrix,Boolean.W,map_prod,apply_ite,hrK]
  let B : Matrix ((Fin k ⊕ Fin l) × Boolean.Cube d) ((Fin k ⊕ Fin l) × Boolean.Cube d) K₀ :=
    MultiGraph.tensorInteraction (matrix aK bK) T
  have hmatrix (i j : (Fin k ⊕ Fin l) × Boolean.Cube d) :
      (B i j:ℝ)=matrix a b i.1 j.1*Boolean.tensor ρ i.2 j.2 := by
    rcases i with ⟨i,x⟩
    rcases j with ⟨j,y⟩
    cases i <;> cases j <;> simp [B,MultiGraph.tensorInteraction,matrix,hT,hpK]
  have hm : M=fun i j=>B (e i) (e j) := by
    funext i j
    apply Subtype.ext
    have h := he (e i) (e j)
    simp only [e.symm_apply_apply] at h
    exact h.trans (hmatrix (e i) (e j)).symm
  have hw : w=fun i=>Sum.elim μK νK (e i).1 := by
    funext i
    apply Subtype.ext
    rw [hweight]
    cases h : (e i).1 with
    | inl j => exact (hμK j).symm
    | inr j => exact (hνK j).symm
  have hTfp : (evaluationProblem basis (fun _:Fin 1=>T) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP :=
    BooleanTensorFPClosure.tensor_inFP basis (fun r=>isingMatrix (ρK r))
      (fun r=>hIsing K₀ dimension basis (ρK r) (by rw [hrK]; exact hρ r))
  have hBfp : (evaluationProblem basis (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0)
      (fun p=>Sum.elim μK νK p.1)).InFP := by
    have h := WeightedBlockTractability.product_inFP basis (matrix aK bK) T
      (Sum.elim μK νK) (fun _=>1) (evaluation_inFP basis aK μK bK νK) hTfp
    have hw1 : MultiGraph.tensorVertexWeight (Sum.elim μK νK) (fun _:Boolean.Cube d=>(1:K₀)) =
        (fun p : (Fin k ⊕ Fin l) × Boolean.Cube d=>Sum.elim μK νK p.1) := by
      funext p
      exact mul_one _
    rw [hw1] at h
    exact h
  rw [hm,hw]
  exact WeightedBlockTractability.color_inFP basis e B (fun p=>Sum.elim μK νK p.1) hBfp

theorem source_ising_tensor_inFP_of_ising (hIsing : PositiveIsingFoundation)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀)
    (i0 : Fin k) (j0 : Fin l) (e : C ≃ (Fin k ⊕ Fin l) × Boolean.Cube d)
    (a : Fin k → ℝ) (ha : ∀i,0<a i) (b : Fin l → ℝ) (hb : ∀j,0<b j)
    (ρ : Fin d → ℝ) (hρ : ∀r,0<ρ r)
    (hsource : Matrix.reindex e e (fun i j=>(M i j:ℝ)) =
      MultiGraph.tensorInteraction (matrix a b) (Boolean.tensor ρ)) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  apply source_weighted_ising_tensor_inFP_of_ising hIsing K₀ basis M (fun _=>1) i0 j0 e a ha b hb ρ hρ
    (fun _=>1) (fun _=>1) hsource
  intro i
  cases (e i).1 <;> rfl

end PlanarHom.BipartiteRankTwoTractability

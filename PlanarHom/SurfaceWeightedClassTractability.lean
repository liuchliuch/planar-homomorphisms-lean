import PlanarHom.SurfacePositiveBlockSource
import PlanarHom.SurfaceBipartiteBlockSource
import PlanarHom.SurfaceComponentClosure
import PlanarHom.WeightedBlockTractabilityConditional

/-! NEW supplied-row weighted block composition, with the literal source forms and masses unchanged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Classical
namespace PlanarHom.SurfaceWeightedBlockTractability
open Complexity Complexity.MixedCode Structures BooleanTensorEasyAssembly SurfaceRowEvaluation
variable {ambient : ℕ}
variable {C : Type} [Fintype C] {dimension : ℕ}

theorem allowedWeightedBlock_inFP_of_ising (hIsing : SurfaceRowEvaluation.PositiveIsingFoundation ambient)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀) (w : C → K₀)
    (h : AllowedWeightedBlock (fun i j=>(M i j:ℝ)) (fun i=>(w i:ℝ))) :
    (SurfaceRowEvaluation.Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) := by
  cases h with
  | zero e hz hw =>
    have hm : M=0 := by
      funext i j
      exact Subtype.ext (hz i j)
    let f : C ≃ Fin 1 := e.trans (Equiv.ofUnique Unit (Fin 1))
    have hf := color_inFP (ambient:=ambient) basis f (fun _ _ : Fin 1=>(0:K₀)*(0:K₀)) (fun i=>w (f.symm i))
      (SurfaceWeightedBlockTractability.rankOne_inFP basis (fun _:Fin 1=>(0:K₀)) (fun i=>w (f.symm i)))
    simpa only [hm,zero_mul,f.symm_apply_apply,Matrix.zero_apply] using hf
  | positive k d hk a mass ρ ha hmass hρ e hm hw =>
    apply source_positive_block_inFP_of_ising hIsing K₀ basis M w ⟨0,hk⟩ e a mass ha ρ
      (fun r=>(hρ r).1) _ hw
    ext i j
    simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,e.apply_symm_apply] using hm (e.symm i) (e.symm j)
  | bipartite k l d hk hl a massX b massY ρ ha hb hmx hmy hρ e hm hw =>
    apply SurfaceBipartiteRankTwoTractability.source_weighted_ising_tensor_inFP_of_ising
      hIsing K₀ basis M w ⟨0,hk⟩ ⟨0,hl⟩ e a ha b hb ρ (fun r=>(hρ r).1) massX massY _ hw
    ext i j
    have h := hm (e.symm i) (e.symm j)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,e.apply_symm_apply] at h ⊢
    exact h

theorem weightedClass_inFP_of_ising (hIsing : SurfaceRowEvaluation.PositiveIsingFoundation ambient)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀) (w : C → K₀)
    (h : WeightedClass (fun i j=>(M i j:ℝ)) (fun i=>(w i:ℝ))) :
    (SurfaceRowEvaluation.Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) := by
  have hs : ∀i j,(M i j:ℝ)=(M j i:ℝ) :=
    Structures.NonnegativeClass.symmetric (Structures.WeightedClass.unweighted h)
  obtain ⟨t,block,honto,hzero,hforms⟩ := h
  letI : DecidableEq (Fin t) := Classical.decEq _
  have hsK : ∀i j,M i j=M j i := fun i j=>Subtype.ext (hs i j)
  have hzK : ∀i j,block i≠block j→M i j=0 := fun i j hij=>Subtype.ext (hzero i j hij)
  apply SurfaceRowEvaluation.fibers_inFP ambient basis block M hsK hzK w
  intro r
  exact allowedWeightedBlock_inFP_of_ising hIsing K₀ basis
    (fun i j : {i // block i=r}=>M i.val j.val) (fun i=>w i.val) (hforms r)

end PlanarHom.SurfaceWeightedBlockTractability

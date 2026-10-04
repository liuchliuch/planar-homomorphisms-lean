import PlanarHom.SurfaceWeightedClassTractability

/-! NEW full nonnegative structural sufficiency on supplied rows, with
component extraction retaining the proved ambient homology bound. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.SurfaceWeightedBlockTractability
open Complexity Complexity.MixedCode Structures SurfaceRowEvaluation
variable {ambient:ℕ} {C:Type} [Fintype C] {dimension:ℕ}

theorem allowedBlock_inFP_of_ising (hIsing:PositiveIsingFoundation ambient)
    (K₀:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis:Module.Basis (Fin dimension) ℚ K₀) (M:Matrix C C K₀)
    (h:AllowedBlock (fun i j=>(M i j:ℝ))) :
    Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1) := by
  cases h with
  | zero e hz =>
    have hm:M=0:=by funext i j;exact Subtype.ext (hz i j)
    let f:C≃Fin 1:=e.trans (Equiv.ofUnique Unit (Fin 1))
    have hf:=color_inFP (ambient:=ambient) basis f (fun _ _:Fin 1=>(0:K₀)*(0:K₀)) (fun _=>1)
      (rankOne_inFP basis (fun _:Fin 1=>(0:K₀)) (fun _=>1))
    simpa only [hm,zero_mul,Matrix.zero_apply] using hf
  | positive k d hk a ρ ha hρ e hm =>
    apply source_positive_block_inFP_of_ising hIsing K₀ basis M (fun _=>1)
      ⟨0,hk⟩ e a (fun _=>1) ha ρ hρ _ (fun _=>rfl)
    ext i j
    simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,e.apply_symm_apply] using hm (e.symm i) (e.symm j)
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    apply SurfaceBipartiteRankTwoTractability.source_weighted_ising_tensor_inFP_of_ising
      hIsing K₀ basis M (fun _=>1) ⟨0,hk⟩ ⟨0,hl⟩ e a ha b hb ρ hρ (fun _=>1) (fun _=>1)
    · ext i j
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,e.apply_symm_apply] using hm (e.symm i) (e.symm j)
    · intro i
      cases (e i).1 <;> rfl

theorem nonnegativeClass_inFP_of_ising (hIsing:PositiveIsingFoundation ambient)
    (K₀:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis:Module.Basis (Fin dimension) ℚ K₀) (M:Matrix C C K₀)
    (h:NonnegativeClass (fun i j=>(M i j:ℝ))) :
    Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1) := by
  have hs:=h.symmetric
  obtain ⟨t,block,honto,hzero,hforms⟩:=h
  letI : DecidableEq (Fin t):=Classical.decEq _
  apply SurfaceRowEvaluation.fibers_inFP ambient basis block M
    (fun i j=>Subtype.ext (hs i j)) (fun i j h=>Subtype.ext (hzero i j h)) (fun _=>1)
  intro r
  exact allowedBlock_inFP_of_ising hIsing K₀ basis
    (fun i j:{i // block i=r}=>M i.val j.val) (hforms r)

end PlanarHom.SurfaceWeightedBlockTractability

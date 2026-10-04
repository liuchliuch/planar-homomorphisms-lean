import PlanarHom.LowRankMatrixMinors
import PlanarHom.BipartiteRankTwoEvaluationMachines
import PlanarHom.BooleanTensorFPClosure

/-! NEW original-field algorithms for the literal low-rank alternatives in
Proposition 2.5(ii), including zero rows and rectangular rank-one blocks. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
open Complexity Complexity.MixedCode
variable {C:Type} [Fintype C] {dimension:ℕ}

 def RankBlock (M:Matrix C C ℝ) : Prop :=
  M.rank=0 ∨ M.rank=1 ∨ ∃k l,∃V:Matrix (Fin k) (Fin l) ℝ,∃e:C≃Fin k⊕Fin l,
    V.rank=1 ∧ ∀i j,M i j=(Matrix.fromBlocks 0 V V.transpose 0) (e i) (e j)

 theorem RankBlock.changeFintype {C:Type} {f g:Fintype C} {M:Matrix C C ℝ}
    (h:@RankBlock C f M) : @RankBlock C g M := by
  cases Subsingleton.elim f g
  exact h

 theorem rankOne_generic_inFP (K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (basis:Module.Basis (Fin dimension) ℚ K) (a:C→K) :
    (evaluationProblem basis (fun _:Fin 1=>fun i j=>a i*a j) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  let e:=Fintype.equivFin C
  have hf:=RankOneEvaluationMachine.evaluation_inFP basis (fun i=>a (e.symm i)) (fun _=>1)
  have hh:=BooleanTensorFPClosure.color_inFP basis e (fun i j=>a (e.symm i)*a (e.symm j)) hf
  simpa only [Equiv.symm_apply_apply] using hh

 theorem zero_rank_block_inFP (K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (basis:Module.Basis (Fin dimension) ℚ K) (M:Matrix C C K)
    (hr:Matrix.rank (fun i j=>(M i j:ℝ))=0) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  have hm:M=0:=by
    funext i j
    exact Subtype.ext (congrArg (fun A:Matrix C C ℝ=>A i j) (matrix_zero_of_rank_zero _ hr))
  have hf:=rankOne_generic_inFP K basis (fun _:C=>(0:K))
  simpa only [hm,zero_mul,Matrix.zero_apply] using hf

 theorem symmetric_rank_one_block_inFP (K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (basis:Module.Basis (Fin dimension) ℚ K) (M:Matrix C C K)
    (hs:∀i j,(M i j:ℝ)=(M j i:ℝ)) (hr:Matrix.rank (fun i j=>(M i j:ℝ))=1) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  let R:Matrix C C ℝ:=fun i j=>(M i j:ℝ)
  have hrR:R.rank=1:=hr
  have hsR:∀i j,R i j=R j i:=hs
  obtain ⟨r,hn⟩:=symmetric_rank_one_nonzero_diagonal R hs hr
  let a:C→K:=fun i=>M i r
  let γ:K:=(M r r)⁻¹
  let A:Matrix C C K:=fun i j=>a i*a j
  have hm:M=γ • A:=by
    funext i j
    apply Subtype.ext
    change R i j=(R r r)⁻¹*(R i r*R j r)
    calc
      _ = (R i r*R r j)/R r r := (eq_div_iff hn).mpr (two_minor_zero_of_rank_le_one R (by omega) i j r)
      _ = _ := by rw [hsR r j];ring
  have hf:=BooleanTensorFPClosure.scalar_inFP basis γ A
    (rankOne_generic_inFP K basis a)
  rw [hm]
  exact hf

 theorem rectangular_rank_one_block_inFP (K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (basis:Module.Basis (Fin dimension) ℚ K) (M:Matrix C C K) {k l:ℕ}
    (V:Matrix (Fin k) (Fin l) ℝ) (e:C≃Fin k⊕Fin l) (hr:V.rank=1)
    (hM:∀i j,(M i j:ℝ)=(Matrix.fromBlocks 0 V V.transpose 0) (e i) (e j)) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  obtain ⟨r,s,hn⟩:=exists_nonzero_entry_of_rank_one V hr
  let VK:Matrix (Fin k) (Fin l) K:=fun i j=>M (e.symm (.inl i)) (e.symm (.inr j))
  have hV:∀i j,(VK i j:ℝ)=V i j:=by
    intro i j
    simp only [VK,hM,Equiv.apply_symm_apply,Matrix.fromBlocks_apply₁₂]
  let a:Fin k→K:=fun i=>VK i s
  let b:Fin l→K:=fun j=>VK r j/VK r s
  have hab (i:Fin k) (j:Fin l):(a i*b j:K)=VK i j:=by
    apply Subtype.ext
    change (VK i s:ℝ)*((VK r j:ℝ)/(VK r s:ℝ))=(VK i j:ℝ)
    rw [hV,hV,hV,hV,←mul_div_assoc]
    exact ((eq_div_iff hn).mpr (rectangular_minor_zero_of_rank_le_one V (by omega) i r j s)).symm
  let B:=BipartiteRankTwoTractability.matrix a b
  have hB:∀i j,(B i j:ℝ)=(Matrix.fromBlocks 0 V V.transpose 0) i j:=by
    intro i j
    cases i <;> cases j <;> simp [B,BipartiteRankTwoTractability.matrix,hab,hV]
  have hm:M=fun i j=>B (e i) (e j):=by
    funext i j
    exact Subtype.ext ((hM i j).trans (hB (e i) (e j)).symm)
  have hf:=BipartiteRankTwoTractability.evaluation_inFP basis a (fun _=>1) b (fun _=>1)
  have hw:(Sum.elim (fun _:Fin k=>(1:K)) (fun _:Fin l=>(1:K)))=(fun _=>1):=by
    funext i
    cases i <;> rfl
  rw [hw] at hf
  rw [hm]
  exact BooleanTensorFPClosure.color_inFP basis e B hf

 theorem rankBlock_inFP (K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (basis:Module.Basis (Fin dimension) ℚ K) (M:Matrix C C K)
    (hs:∀i j,(M i j:ℝ)=(M j i:ℝ)) (hr:RankBlock (fun i j=>(M i j:ℝ))) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP := by
  rcases hr with hr|hr|⟨k,l,V,e,hr,hm⟩
  · exact zero_rank_block_inFP K basis M hr
  · exact symmetric_rank_one_block_inFP K basis M hs hr
  · exact rectangular_rank_one_block_inFP K basis M V e hr hm

end PlanarHom.GadgetDiagonalSeparation

import PlanarHom.SignedThreeStateCriterion
import PlanarHom.SignedIrreducibleThreeHardness
import PlanarHom.SignedBlockHardness

/-! Complete exact signed three-state hard complement in the main-text
algebraic bit model. The fixed-real extension remains an appendix obligation. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure ThreeStateDimension
variable {F : IntermediateField ℚ ℝ} [FiniteDimensional ℚ F] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ F)

/-- Every signed symmetric 3×3 matrix outside the three exact alternatives is
#P-hard on ordinary raw planar inputs, through actual Turing reductions. -/
theorem signed_three_hard (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i) (hh : ¬ThreeStateEasy (fun i j=>(M i j:ℝ))) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1)) := by
  have hr : ¬Matrix.rank (fun i j=>(M i j:ℝ))≤1 := fun h=>hh (Or.inl h)
  have hst : ¬PermutedStar (fun i j=>(M i j:ℝ)) := fun h=>hh (Or.inr (Or.inr h))
  by_cases hi : NoBooleanZeroCut (fun i j=>(M i j:ℝ))
  · exact irreducible_signed_three_hard basis M hs hi hr hst
  · obtain ⟨p,hp⟩ := isolated_color_of_reducible (fun i j=>(M i j:ℝ)) hi
    have hpF : ∀j,j≠p→M p j=0 := fun j hj=>Subtype.ext (hp j hj)
    obtain ⟨a,b,c,t,e,hm⟩ := block_of_isolated M hs p hpF
    have hb : ¬BooleanEasy (a:ℝ) (b:ℝ) (c:ℝ) := by
      intro heasy
      apply hh
      refine Or.inr (Or.inl ⟨(a:ℝ),(b:ℝ),(c:ℝ),(t:ℝ),heasy,e,?_⟩)
      intro i j
      change (M i j:ℝ)=_
      rw [hm]
      generalize e i=x
      generalize e j=y
      fin_cases x <;> fin_cases y <;> rfl
    have he : M=(fun i j=>blockMatrix a b c t (e i) (e j)) := funext (fun i=>funext (hm i))
    rw [he,homogeneous_problem_reindex]
    exact signed_boolean_block_hard basis a b c t hb

end PlanarHom.SignedThreeState

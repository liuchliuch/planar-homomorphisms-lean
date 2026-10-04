import PlanarHom.SignedThreeSignGram
import PlanarHom.SignedSourceGadgetReductions
import PlanarHom.ThreeStatePositiveRank
import PlanarHom.MainDichotomiesClosed
import PlanarHom.AlgebraicLanguagePresentation

/-! A genuine signed hardness branch: full support, rank-one squared
magnitudes, and rank greater than one. The source is reduced through actual
sign interpolation, path substitution and thickening to a positive three-state
matrix outside the proved structural class. This is not the full 2.3 theorem. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
variable {F : IntermediateField ℚ ℝ} [FiniteDimensional ℚ F] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ F)

/-- Main 1.1 plus its proved odd three-color dimension consequence, transported
back to any prescribed exact finite source-field presentation. -/
theorem positive_three_hard (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i) (hp : ∀i j,0<(M i j:ℝ))
    (hr : ¬Matrix.rank (fun i j=>(M i j:ℝ))≤1) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  let L : RealLanguage 3 1 0 := {
    matrices := fun _ i j=>(M i j:ℝ)
    unaries := fun i=>i.elim0
    weights := fun _=>1
    matrices_algebraic := fun _ i j=>(IsAlgebraic.of_finite ℚ (M i j)).algHom F.val
    unaries_algebraic := fun i=>i.elim0
    weights_algebraic := fun _=>isAlgebraic_one }
  have hh := (MainDichotomyScope.theorem11 L (fun _=>rfl)
    (fun i j=>congrArg Subtype.val (hs i j)) (fun i j=>(hp i j).le)).2
  have hhard : PromisedSharpPHard L.problem := hh (fun hc=>hr
    (ThreeStateDimension.positive_nonnegativeClass_rank_le_one hp hc))
  exact hhard.trans (L.presentationDescentReduction F basis (fun _:Fin 1=>M)
    BooleanTensorFPClosure.emptyUnaries (fun _=>1) (fun _ _ _=>rfl)
    (fun i=>i.elim0) (fun _=>rfl))

/-- Closed fixed-field signed branch, with no numerical matrix or algorithm
supplied as an extra oracle. -/
theorem magnitude_rank_one_signed_hard (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i) (hn : ∀i j,M i j≠0)
    (hmag : (schurSquare (fun i j=>(M i j:ℝ))).rank≤1)
    (hr : ¬Matrix.rank (fun i j=>(M i j:ℝ))≤1) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  let S := MagnitudeSign.signMatrix M
  let B := schurSquare (S*S)
  have hm : (fun i j=>(B i j:ℝ))=
      schurSquare (realSignMatrix (fun i j=>(M i j:ℝ))*
        realSignMatrix (fun i j=>(M i j:ℝ))) := by
    funext i j
    simp [B,S,schurSquare,Matrix.mul_apply,realSignMatrix,MagnitudeSign.signMatrix,
      ←MagnitudeSign.sign_coe,map_sum,map_mul,map_pow]
  have hreal := signed_magnitude_rank_one_target (fun i j=>(M i j:ℝ))
    (fun i j=>congrArg Subtype.val (hs i j))
    (fun i j h=>hn i j (Subtype.ext h)) hmag hr
  have hb : ∀i j,B i j=B j i := by
    intro i j
    apply Subtype.ext
    have hs' : ∀i j,realSignMatrix (fun i j=>(M i j:ℝ)) i j=
        realSignMatrix (fun i j=>(M i j:ℝ)) j i := by
      intro i j
      simp [realSignMatrix,hs i j]
    have h := congrFun (congrFun hm i) j
    have h' := congrFun (congrFun hm j) i
    rw [h,h',signGram_square_eq _ hs']
    simp only [schurSquare,rowGram_symmetric]
  have hh : PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>B)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) :=
    positive_three_hard basis B hb (by
      intro i j
      change 0<(fun i j=>(B i j:ℝ)) i j
      rw [hm]
      exact hreal.1 i j)
      (by rw [hm]; exact hreal.2)
  exact hh.trans (signSquaredGramReduction basis M BooleanTensorFPClosure.emptyUnaries)


/-- Complete higher-rank hardness on the signed full-support three-state
stratum. Entrywise square is used only as a proved planar reduction. -/
theorem full_support_signed_three_hard (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i) (hn : ∀i j,M i j≠0)
    (hr : ¬Matrix.rank (fun i j=>(M i j:ℝ))≤1) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  by_cases hmag : (schurSquare (fun i j=>(M i j:ℝ))).rank≤1
  · exact magnitude_rank_one_signed_hard basis M hs hn hmag hr
  have hp : ∀i j,0<(schurSquare M i j:ℝ) := by
    intro i j
    change 0<(M i j:ℝ)^2
    apply sq_pos_of_ne_zero
    exact fun h=>hn i j (Subtype.ext h)
  have hs' : ∀i j,schurSquare M i j=schurSquare M j i := by
    intro i j
    simp only [schurSquare,hs i j]
  have hh := positive_three_hard basis (schurSquare M) hs' hp hmag
  exact hh.trans (squareReduction basis M BooleanTensorFPClosure.emptyUnaries (fun _=>1))

end PlanarHom.SignedThreeState

import PlanarHom.SignedThreeStateHardness
import PlanarHom.SignedThreeSupportAlgebra

/-! Complete signed irreducible three-state hardness. The only excluded
structures are the exact rank-one and signed-star alternatives of 2.3. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode AlgebraicProductInterpolation Structures ThreeStateDimension
variable {F : IntermediateField ℚ ℝ} [FiniteDimensional ℚ F] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ F)

theorem nonnegative_field_hard {q : ℕ} (M : Matrix (Fin q) (Fin q) F)
    (hs : ∀i j,M i j=M j i) (hp : ∀i j,0≤(M i j:ℝ))
    (hc : ¬NonnegativeClass (fun i j=>(M i j:ℝ))) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  let L : RealLanguage q 1 0 := {
    matrices := fun _ i j=>(M i j:ℝ)
    unaries := fun i=>i.elim0
    weights := fun _=>1
    matrices_algebraic := fun _ i j=>(IsAlgebraic.of_finite ℚ (M i j)).algHom F.val
    unaries_algebraic := fun i=>i.elim0
    weights_algebraic := fun _=>isAlgebraic_one }
  have hh : PromisedSharpPHard L.problem := (MainDichotomyScope.theorem11 L (fun _=>rfl)
    (fun i j=>congrArg Subtype.val (hs i j)) hp).2 hc
  exact hh.trans (L.presentationDescentReduction F basis (fun _:Fin 1=>M)
    BooleanTensorFPClosure.emptyUnaries (fun _=>1) (fun _ _ _=>rfl)
    (fun i=>i.elim0) (fun _=>rfl))

/-- Neither nonnegativity nor full support is assumed on the signed source.
All hardness is routed through actual polynomial planar gadget reductions. -/
theorem irreducible_signed_three_hard (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i)
    (hi : NoBooleanZeroCut (fun i j=>(M i j:ℝ)))
    (hr : ¬Matrix.rank (fun i j=>(M i j:ℝ))≤1)
    (hst : ¬PermutedStar (fun i j=>(M i j:ℝ))) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>M)
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  let A := schurSquare M
  have hsym : ∀i j,(M i j:ℝ)=(M j i:ℝ) := fun i j=>congrArg Subtype.val (hs i j)
  have hAs : ∀i j,A i j=A j i := by intro i j; simp [A,schurSquare,hs i j]
  have hcut : NoBooleanZeroCut (schurSquare (fun i j=>(M i j:ℝ))) :=
    (noBooleanZeroCut_square_iff _).mpr hi
  by_cases hc : NonnegativeClass (schurSquare (fun i j=>(M i j:ℝ)))
  · rcases nonnegativeClass_three_rank_or_star hcut hc with h1|⟨a,b,e,ha,hb,hstar⟩
    · have hn := rank_one_no_cut_full_support (schurSquare (fun i j=>(M i j:ℝ)))
        (fun i j=>congrArg (fun x:ℝ=>x^2) (hsym i j)) hcut h1
      apply full_support_signed_three_hard basis M hs _ hr
      intro i j h
      apply hn i j
      simp [schurSquare,h]
    · exact False.elim (hst (permutedStar_of_squared_permutedStar _ hsym ⟨a,b,e,hstar⟩))
  · have hh : PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>A)
        BooleanTensorFPClosure.emptyUnaries (fun _=>1)) :=
      nonnegative_field_hard basis A hAs (fun i j=>sq_nonneg (M i j:ℝ)) hc
    exact hh.trans (squareReduction basis M BooleanTensorFPClosure.emptyUnaries (fun _=>1))

end PlanarHom.SignedThreeState

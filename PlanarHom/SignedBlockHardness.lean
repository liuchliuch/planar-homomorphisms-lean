import PlanarHom.SignedBlockTractability
import PlanarHom.SignedBooleanHardness
import PlanarHom.SupportComponentReduction
import Mathlib.Algebra.Order.Field.Subfield

/-! Actual signed Boolean-block hardness survives an arbitrary scalar direct
summand. Component extraction and color-codec equality supply the reduction. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {K C D : Type} [Field K] [Algebra ℚ K] [Fintype C] [Fintype D]
variable {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

theorem homogeneous_problem_reindex (e : C≃D) (M : Matrix D D K) :
    evaluationProblem basis (fun _:Fin 1=>fun i j=>M (e i) (e j)) emptyUnaries (fun _=>1)=
      evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1) := by
  have h := evaluationProblem_colorReindex basis e (fun _:Fin 1=>M) (emptyUnaries : Fin 0→D→K) (fun _=>1)
  have hu : (fun (l:Fin 0) (i:C)=>emptyUnaries l (e i))=(emptyUnaries : Fin 0→C→K) := by
    funext l
    exact l.elim0
  rw [hu] at h
  exact h

section Fiber
local instance (priority := 10000) hardBlockDecEq (α : Type*) : DecidableEq α := Classical.decEq α
variable [LinearOrder K] [IsStrictOrderedRing K]

def directSum_left_reduction (A : Matrix C C K) (B : Matrix D D K)
    (hsA : ∀i j,A i j=A j i) (hsB : ∀i j,B i j=B j i) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>A) emptyUnaries (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>Matrix.fromBlocks A 0 0 B) emptyUnaries (fun _=>1)) := by
  let M := Matrix.fromBlocks A 0 0 B
  let X : Set (C⊕D) := {x | x.isRight=false}
  have hs : ∀i j,M i j=M j i := by
    intro i j
    cases i <;> cases j <;> simp [M,Matrix.fromBlocks,hsA,hsB]
  have hx : RootedRestriction.ColorClosed M X := by
    intro i hi j hn
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact False.elim (hn rfl)
    | inr i => exact Bool.noConfusion hi
  have hh := RootedRestriction.submatrixReduction basis M hs (fun _=>1) (fun _=>zero_lt_one) X hx
  have hm : (fun i j : X=>M i.val j.val)=(fun i j=>A (leftSumFiber i) (leftSumFiber j)) := by
    funext ⟨i,hi⟩ ⟨j,hj⟩
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact Bool.noConfusion hj
    | inr i => exact Bool.noConfusion hi
  have hf : (fun _:Fin 1=>fun i j : X=>M i.val j.val)=
      (fun _:Fin 1=>fun i j=>A (leftSumFiber i) (leftSumFiber j)) := funext (fun _=>hm)
  rw [hf] at hh
  have he := homogeneous_problem_reindex basis (leftSumFiber : X≃C) A
  change PromisePolyTimeTuringReduction
    (evaluationProblem basis (fun _:Fin 1=>fun i j=>A (leftSumFiber i) (leftSumFiber j)) emptyUnaries (fun _=>1)) _ at hh
  rw [he] at hh
  exact hh
end Fiber

/-- The scalar summand has no sign or nonzero constraint. -/
theorem signed_boolean_block_hard {F : IntermediateField ℚ ℝ} [FiniteDimensional ℚ F]
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ F)
    (a b c t : F) (h : ¬BooleanEasy (a:ℝ) (b:ℝ) (c:ℝ)) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>blockMatrix a b c t)
      emptyUnaries (fun _=>1)) := by
  letI : IsStrictOrderedRing F := Subfield.toIsStrictOrderedRing F.toSubfield
  have hh := (signed_boolean_hard basis a b c h).trans
    (directSum_left_reduction basis (booleanMatrix a b c) (fun _ _ : Fin 1=>t)
      (by intro i j; fin_cases i <;> fin_cases j <;> rfl) (fun _ _=>rfl))
  have hm : blockMatrix a b c t=(fun i j=>
      (Matrix.fromBlocks (booleanMatrix a b c) 0 0 (fun _ _ : Fin 1=>t))
        (threeStarColors i) (threeStarColors j)) := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm,homogeneous_problem_reindex]
  exact hh

end PlanarHom.SignedThreeState

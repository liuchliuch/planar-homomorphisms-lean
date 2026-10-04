import PlanarHom.SignedSmallStateTractability
import PlanarHom.TractableBlockComposition

/-! Actual direct-sum closure and all elementary signed Boolean cases in a
prescribed fixed field. The scalar third block is unrestricted. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {K C D : Type} [Field K] [Algebra ℚ K] [Fintype C] [Fintype D]
variable {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

def leftSumFiber : {x : C⊕D // x.isRight=false} ≃ C where
  toFun := by
    rintro ⟨x,h⟩
    cases x with
    | inl c => exact c
    | inr d => simp at h
  invFun c := ⟨.inl c,rfl⟩
  left_inv := by
    rintro ⟨x,h⟩
    cases x with
    | inl c => rfl
    | inr d => simp at h
  right_inv c := rfl

def rightSumFiber : {x : C⊕D // x.isRight=true} ≃ D where
  toFun := by
    rintro ⟨x,h⟩
    cases x with
    | inl c => simp at h
    | inr d => exact d
  invFun d := ⟨.inr d,rfl⟩
  left_inv := by
    rintro ⟨x,h⟩
    cases x with
    | inl c => simp at h
    | inr d => rfl
  right_inv d := rfl

section FiberCompiler
local instance (priority := 10000) localDecEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Arbitrary signed direct sums are evaluated componentwise by real TM2
programs; symmetry is the only algebraic constraint on the summands. -/
theorem signed_directSum_inFP (A : Matrix C C K) (B : Matrix D D K)
    (hAs : ∀i j,A i j=A j i) (hBs : ∀i j,B i j=B j i)
    (hA : (evaluationProblem basis (fun _:Fin 1=>A) emptyUnaries (fun _=>1)).InFP)
    (hB : (evaluationProblem basis (fun _:Fin 1=>B) emptyUnaries (fun _=>1)).InFP) :
    (evaluationProblem basis (fun _:Fin 1=>Matrix.fromBlocks A 0 0 B)
      emptyUnaries (fun _=>1)).InFP := by
  apply TractableBlockComposition.fibers_inFP basis Sum.isRight
  · intro i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,hAs,hBs]
  · intro i j h
    cases i <;> cases j <;> simp_all [Matrix.fromBlocks]
  · intro b
    cases b
    · have hm : (fun i j : {x : C⊕D // x.isRight=false}=>
          (Matrix.fromBlocks A 0 0 B) i.val j.val)=
          (fun i j=>A (leftSumFiber i) (leftSumFiber j)) := by
        funext ⟨i,hi⟩ ⟨j,hj⟩
        cases i with
        | inl i =>
          cases j with
          | inl j => rfl
          | inr j => exact Bool.noConfusion hj
        | inr i => exact Bool.noConfusion hi
      have hf : (fun _ : Fin 1=>fun i j : {x : C⊕D // x.isRight=false}=>
          (Matrix.fromBlocks A 0 0 B) i.val j.val)=
          (fun _ : Fin 1=>fun i j=>A (leftSumFiber i) (leftSumFiber j)) := funext (fun _=>hm)
      rw [hf]
      exact color_inFP basis leftSumFiber A hA
    · have hm : (fun i j : {x : C⊕D // x.isRight=true}=>
          (Matrix.fromBlocks A 0 0 B) i.val j.val)=
          (fun i j=>B (rightSumFiber i) (rightSumFiber j)) := by
        funext ⟨i,hi⟩ ⟨j,hj⟩
        cases i with
        | inl i => exact Bool.noConfusion hi
        | inr i =>
          cases j with
          | inl j => exact Bool.noConfusion hj
          | inr j => rfl
      have hf : (fun _ : Fin 1=>fun i j : {x : C⊕D // x.isRight=true}=>
          (Matrix.fromBlocks A 0 0 B) i.val j.val)=
          (fun _ : Fin 1=>fun i j=>B (rightSumFiber i) (rightSumFiber j)) := funext (fun _=>hm)
      rw [hf]
      exact color_inFP basis rightSumFiber B hB

end FiberCompiler

/-- The singleton fixed scalar can be zero, positive or negative. -/
theorem singleton_inFP (t : K) :
    (evaluationProblem basis (fun _:Fin 1=>fun _ _ : Fin 1=>t)
      emptyUnaries (fun _=>1)).InFP := by
  have hm : (fun _ _ : Fin 1=>t)=t • (fun _ _ : Fin 1=>(1:K)*(1:K)) := by
    funext i j
    simp
  rw [hm]
  exact signed_scalar_rankOne_inFP basis t (fun _=>1)

/-- Exact diagonal Boolean branch with two arbitrary signed diagonal values. -/
theorem diagonal_boolean_inFP (a c : K) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a 0 c)
      emptyUnaries (fun _=>1)).InFP := by
  have h := signed_directSum_inFP basis (fun _ _ : Fin 1=>a) (fun _ _ : Fin 1=>c)
    (fun _ _=>rfl) (fun _ _=>rfl) (singleton_inFP basis a) (singleton_inFP basis c)
  have hm : booleanBool a 0 c=(fun i j=>
      (Matrix.fromBlocks (fun _ _ : Fin 1=>a) 0 0 (fun _ _ : Fin 1=>c))
        (boolSumOne i) (boolSumOne j)) := by
    funext i j
    cases i <;> cases j <;> rfl
  rw [hm]
  exact color_inFP basis boolSumOne _ h

/-- Exact determinant-zero Boolean branch, including negative rank-one. -/
theorem rankOne_boolean_inFP (a b c : K) (h : a*c=b^2) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a b c)
      emptyUnaries (fun _=>1)).InFP := by
  by_cases ha : a=0
  · subst a
    have hb : b=0 := by simpa using (sq_eq_zero_iff.mp (by simpa using h.symm))
    subst b
    exact diagonal_boolean_inFP basis 0 c
  have hm : booleanBool a b c=a⁻¹ • (fun i j : Bool=>
      (if i then b else a)*(if j then b else a)) := by
    funext i j
    cases i <;> cases j <;> simp [booleanBool,Pi.smul_apply,smul_eq_mul]
    · field_simp
    · field_simp
    · field_simp
    · apply mul_left_cancel₀ ha
      rw [←mul_assoc,mul_inv_cancel₀ ha,one_mul]
      simpa [pow_two] using h
  rw [hm]
  exact finite_signed_scalar_rankOne_inFP (C:=Bool) basis a⁻¹ (fun i : Bool=>if i then b else a)

/-- Adding the third diagonal scalar to any computed Boolean solver is valid
for every signed t, without assuming t is positive or nonzero. -/
theorem two_plus_one_inFP (a b c t : K)
    (h : (evaluationProblem basis (fun _:Fin 1=>booleanBool a b c)
      emptyUnaries (fun _=>1)).InFP) :
    (evaluationProblem basis (fun _:Fin 1=>blockMatrix a b c t)
      emptyUnaries (fun _=>1)).InFP := by
  have hf := color_inFP basis finTwoEquiv (booleanBool a b c) h
  have hm : (fun i j=>booleanBool a b c (finTwoEquiv i) (finTwoEquiv j))=booleanMatrix a b c := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm] at hf
  have hb := signed_directSum_inFP basis (booleanMatrix a b c) (fun _ _ : Fin 1=>t)
    (by intro i j; fin_cases i <;> fin_cases j <;> rfl) (fun _ _=>rfl) hf (singleton_inFP basis t)
  have hm' : blockMatrix a b c t=(fun i j=>
      (Matrix.fromBlocks (booleanMatrix a b c) 0 0 (fun _ _ : Fin 1=>t))
        (threeStarColors i) (threeStarColors j)) := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm']
  exact color_inFP basis threeStarColors _ hb

end PlanarHom.SignedThreeState

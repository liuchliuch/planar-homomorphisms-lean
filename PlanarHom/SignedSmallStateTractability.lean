import PlanarHom.SignedRankOneAlgebra
import PlanarHom.BooleanTensorFPClosure
import PlanarHom.RankOneEvaluationMachine
import PlanarHom.FKTIsingTractability
import PlanarHom.BipartiteRankTwoEvaluationMachines

/-! Actual fixed-field polynomial algorithms for signed rank-one sources and
signed zero-field Ising, using the already compiled scalar/color machines.
The signed Hadamard branch is deliberately not assumed here. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- This includes negative scalar rank-one interactions. -/
theorem signed_scalar_rankOne_inFP (γ : K) (a : Fin q→K) :
    (evaluationProblem basis (fun _:Fin 1=>γ • (fun i j=>a i*a j))
      emptyUnaries (fun _=>1)).InFP :=
  scalar_inFP basis γ _ (RankOneEvaluationMachine.evaluation_inFP basis a (fun _=>1))

/-- No PSD or nonnegative-entry hypothesis: exact rank≤1 is enough. -/
theorem signed_rank_le_one_inFP (M : Matrix (Fin q) (Fin q) K)
    (hs : ∀i j,M i j=M j i) (hr : M.rank≤1) :
    (evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1)).InFP := by
  rcases scalar_outer_of_rank_le_one M hs hr with hz | ⟨p,hp,hm⟩
  · have hm : M=(0:K) • (fun i j : Fin q=>(1:K)*(1:K)) := by simp [hz]
    rw [hm]
    exact signed_scalar_rankOne_inFP basis 0 (fun _=>1)
  · rw [hm]
    exact signed_scalar_rankOne_inFP basis (M p p)⁻¹ (fun i=>M i p)

/-- Signed Ising parameters are supported by the FKT machine whenever the
high-temperature denominator is nonzero. Positivity is not necessary. -/
theorem signed_ising_inFP [DecidableEq K] (φ : K→+*ℝ) (ρ : K) (hρ : 1+φ ρ≠0) :
    (evaluationProblem basis (fun _:Fin 1=>FKTIsingMachines.matrix ρ)
      emptyUnaries (fun _=>1)).InFP :=
  FKTIsingMachines.ising_inFP basis φ ρ hρ

/-- Arbitrary finite color indexing of a scalar rank-one source. -/
theorem finite_signed_scalar_rankOne_inFP {C : Type} [Fintype C]
    (γ : K) (a : C→K) :
    (evaluationProblem basis (fun _:Fin 1=>γ • (fun i j=>a i*a j))
      emptyUnaries (fun _=>1)).InFP := by
  let e := Fintype.equivFin C
  have h := color_inFP basis e (γ • (fun i j=>a (e.symm i)*a (e.symm j)))
    (signed_scalar_rankOne_inFP basis γ (fun i=>a (e.symm i)))
  simpa only [Pi.smul_apply,smul_eq_mul,e.symm_apply_apply] using h

def booleanBool (a b c : K) : Matrix Bool Bool K :=
  fun i j=>if i then (if j then c else b) else (if j then b else a)

/-- The equal-diagonal family outside its zero pivot and rank-one limits is
an actual signed Ising computation, without entrywise positivity. -/
theorem equal_diagonal_nonzero_inFP [DecidableEq K]
    (φ : K→+*ℝ) (a b : K) (ha : a≠0) (hab : a+b≠0) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a b a)
      emptyUnaries (fun _=>1)).InFP := by
  have hp : 1+φ (b/a)≠0 := by
    intro h
    apply hab
    apply φ.injective
    simp only [map_add,map_zero]
    have ha' : φ a≠0 := (map_ne_zero φ).mpr ha
    rw [map_div₀] at h
    field_simp at h
    nlinarith
  have hm : booleanBool a b a=a • FKTIsingMachines.matrix (b/a) := by
    funext i j
    cases i <;> cases j <;> simp [booleanBool,FKTIsingMachines.matrix,Matrix.smul_apply,smul_eq_mul]
    all_goals field_simp [ha]
  rw [hm]
  exact scalar_inFP basis a _ (signed_ising_inFP basis φ _ hp)

/-- The excluded Ising denominator is an elementary signed rank-one matrix. -/
theorem opposite_equal_diagonal_inFP (a : K) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a (-a) a)
      emptyUnaries (fun _=>1)).InFP := by
  have hm : booleanBool a (-a) a=a • (fun i j : Bool=>
      (if i then (-1:K) else 1)*(if j then (-1:K) else 1)) := by
    funext i j
    cases i <;> cases j <;> simp [booleanBool,Matrix.smul_apply,smul_eq_mul]
  rw [hm]
  exact finite_signed_scalar_rankOne_inFP (C:=Bool) basis a (fun i : Bool=>if i then (-1:K) else 1)


def boolSumOne : Bool ≃ (Fin 1 ⊕ Fin 1) where
  toFun b := if b then .inr 0 else .inl 0
  invFun := Sum.elim (fun _=>false) (fun _=>true)
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b with
    | inl i => fin_cases i; rfl
    | inr i => fin_cases i; rfl

/-- Zero diagonal is the bipartite rank-two algorithm, with arbitrary signed
edge value. No positivity is required by that algorithm. -/
theorem zero_diagonal_inFP (b : K) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool 0 b 0)
      emptyUnaries (fun _=>1)).InFP := by
  have h := BipartiteRankTwoTractability.evaluation_inFP basis
    (fun _ : Fin 1=>b) (fun _=>1) (fun _ : Fin 1=>1) (fun _=>1)
  have hw : (Sum.elim (fun _ : Fin 1=>(1:K)) (fun _ : Fin 1=>1))=(fun _=>1) := by
    funext x
    cases x <;> rfl
  rw [hw] at h
  have hm : booleanBool 0 b 0=(fun i j=>BipartiteRankTwoTractability.matrix
      (fun _ : Fin 1=>b) (fun _ : Fin 1=>1) (boolSumOne i) (boolSumOne j)) := by
    funext i j
    cases i <;> cases j <;> simp [booleanBool,boolSumOne,BipartiteRankTwoTractability.matrix]
  rw [hm]
  exact color_inFP basis boolSumOne _ h

/-- Complete equal-diagonal signed Boolean branch, including zero diagonal
and the singular negative parameter. -/
theorem equal_diagonal_inFP [DecidableEq K] (φ : K→+*ℝ) (a b : K) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a b a)
      emptyUnaries (fun _=>1)).InFP := by
  by_cases ha : a=0
  · subst a
    exact zero_diagonal_inFP basis b
  by_cases hab : a+b=0
  · have hb : b=-a := by linear_combination hab
    rw [hb]
    exact opposite_equal_diagonal_inFP basis a
  exact equal_diagonal_nonzero_inFP basis φ a b ha hab

/-- The 3-state star chart uses unequal side sizes 2+1. -/
def threeStarColors : Fin 3 ≃ (Fin 2 ⊕ Fin 1) where
  toFun := ![.inl 0,.inl 1,.inr 0]
  invFun := Sum.elim (![0,1] : Fin 2→Fin 3) (fun _=>2)
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i; rfl

/-- Theorem 2.3's exact signed star family, including either zero entry. -/
theorem signed_star_inFP (a b : K) :
    (evaluationProblem basis (fun _:Fin 1=>starMatrix a b)
      emptyUnaries (fun _=>1)).InFP := by
  have h := BipartiteRankTwoTractability.evaluation_inFP basis
    (![a,b]) (fun _=>1) (fun _ : Fin 1=>1) (fun _=>1)
  have hw : (Sum.elim (fun _ : Fin 2=>(1:K)) (fun _ : Fin 1=>1))=(fun _=>1) := by
    funext x
    cases x <;> rfl
  rw [hw] at h
  have hm : starMatrix a b=(fun i j=>BipartiteRankTwoTractability.matrix
      (![a,b]) (fun _ : Fin 1=>1) (threeStarColors i) (threeStarColors j)) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [starMatrix,threeStarColors,BipartiteRankTwoTractability.matrix]
  rw [hm]
  exact color_inFP basis threeStarColors _ h

end PlanarHom.SignedThreeState

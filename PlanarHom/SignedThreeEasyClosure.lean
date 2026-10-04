import PlanarHom.SignedThreeStateCriterion
import PlanarHom.SignedBlockHardness
import PlanarHom.SignedHadamardTractability

/-! Complete exact signed three-state easy side in a prescribed fixed field.
The fourth Boolean branch invokes the actual quadratic Gauss-sum machine. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {F : IntermediateField ℚ ℝ} {dimension q : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ F)

def boolFlip : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- The literal signed exceptional branch, including zero scalar. -/
theorem exceptional_boolean_inFP (a b c : F)
    (h : (a:ℝ)*(c:ℝ)=-((b:ℝ)^2) ∧ (a:ℝ)=-(c:ℝ)) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a b c) emptyUnaries (fun _=>1)).InFP := by
  obtain ⟨hc,hb⟩ := (boolean_exceptional_iff (a:ℝ) (b:ℝ) (c:ℝ)).mp h
  have hcF : c=-a := Subtype.ext hc
  rw [hcF]
  rcases hb with hb|hb
  · have hbF : b=a := Subtype.ext hb
    rw [hbF]
    have hm : booleanBool a a (-a)=a • SignedHadamard.interaction := by
      funext i j
      cases i <;> cases j <;> simp [booleanBool,SignedHadamard.interaction,BooleanQuadratic.hadamard]
    rw [hm]
    exact scalar_inFP basis a _ (SignedHadamard.inFP basis)
  · have hbF : b=-a := Subtype.ext hb
    rw [hbF]
    have hm : booleanBool a (-a) (-a)=(fun i j=>
        ((-a) • (SignedHadamard.interaction : Matrix Bool Bool F)) (boolFlip i) (boolFlip j)) := by
      funext i j
      cases i <;> cases j <;> simp [booleanBool,SignedHadamard.interaction,BooleanQuadratic.hadamard,boolFlip]
    rw [hm]
    exact color_inFP basis boolFlip _ (scalar_inFP basis (-a) _ (SignedHadamard.inFP basis))

/-- All four signed Boolean cases, with exact real criteria. -/
theorem signed_boolean_easy_inFP (a b c : F) (h : BooleanEasy (a:ℝ) (b:ℝ) (c:ℝ)) :
    (evaluationProblem basis (fun _:Fin 1=>booleanBool a b c) emptyUnaries (fun _=>1)).InFP := by
  rcases h with h|h|h|h
  · exact rankOne_boolean_inFP basis a b c (Subtype.ext h)
  · have hb : b=0 := Subtype.ext h
    rw [hb]
    exact diagonal_boolean_inFP basis a c
  · have hc : c=a := Subtype.ext h.symm
    rw [hc]
    exact equal_diagonal_inFP basis F.subtype a b
  · exact exceptional_boolean_inFP basis a b c h

/-- A real rank≤1 bound suffices; the pivot factorization is transported to
the original coefficient field rather than assuming a real-arithmetic oracle. -/
theorem real_rank_le_one_inFP (M : Matrix (Fin q) (Fin q) F)
    (hs : ∀i j,M i j=M j i) (hr : Matrix.rank (fun i j=>(M i j:ℝ))≤1) :
    (evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1)).InFP := by
  have hsR : ∀i j,(M i j:ℝ)=(M j i:ℝ) := fun i j=>congrArg Subtype.val (hs i j)
  rcases scalar_outer_of_rank_le_one (fun i j=>(M i j:ℝ)) hsR hr with hz|⟨p,hp,hm⟩
  · have hzero : M=0 := by
      funext i j
      apply Subtype.ext
      exact congrFun (congrFun hz i) j
    have hrF : M.rank≤1 := by rw [hzero,Matrix.rank_zero]; omega
    exact signed_rank_le_one_inFP basis M hs hrF
  · have hpF : M p p≠0 := fun h=>hp (by simpa [h])
    have hminor : ∀i j,M i j*M p p=M i p*M p j := by
      intro i j
      apply Subtype.ext
      exact minor_eq_zero_of_rank_le_one (fun i j=>(M i j:ℝ)) hr i p j p
    have he:=scalar_outer_of_pivot M p hpF hs hminor
    rw [he]
    exact signed_scalar_rankOne_inFP basis (M p p)⁻¹ (fun i=>M i p)

theorem signed_three_easy_inFP (M : Matrix (Fin 3) (Fin 3) F)
    (hs : ∀i j,M i j=M j i) (h : ThreeStateEasy (fun i j=>(M i j:ℝ))) :
    (evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1)).InFP := by
  rcases h with hr|hblock|⟨a,b,e,hm⟩
  · exact real_rank_le_one_inFP basis M hs hr
  · obtain ⟨a,b,c,t,hbool,e,hm⟩:=hblock
    let aF:=M (e.symm 0) (e.symm 0)
    let bF:=M (e.symm 0) (e.symm 1)
    let cF:=M (e.symm 1) (e.symm 1)
    let tF:=M (e.symm 2) (e.symm 2)
    have ha : (aF:ℝ)=a := by simpa [aF,blockMatrix] using hm (e.symm 0) (e.symm 0)
    have hb : (bF:ℝ)=b := by simpa [bF,blockMatrix] using hm (e.symm 0) (e.symm 1)
    have hc : (cF:ℝ)=c := by simpa [cF,blockMatrix] using hm (e.symm 1) (e.symm 1)
    have ht : (tF:ℝ)=t := by simpa [tF,blockMatrix] using hm (e.symm 2) (e.symm 2)
    have he : M=(fun i j=>blockMatrix aF bF cF tF (e i) (e j)) := by
      funext i j
      apply Subtype.ext
      have h:=hm i j
      change (M i j:ℝ)=_ at h ⊢
      rw [h]
      generalize e i=x
      generalize e j=y
      fin_cases x <;> fin_cases y <;> simp [blockMatrix,ha,hb,hc,ht]
    have hbf : BooleanEasy (aF:ℝ) (bF:ℝ) (cF:ℝ) := by simpa only [ha,hb,hc] using hbool
    rw [he]
    exact color_inFP basis e _ (two_plus_one_inFP basis aF bF cF tF
      (signed_boolean_easy_inFP basis aF bF cF hbf))
  · let aF:=M (e.symm 0) (e.symm 2)
    let bF:=M (e.symm 1) (e.symm 2)
    have ha : (aF:ℝ)=a := by simpa [aF,starMatrix] using hm (e.symm 0) (e.symm 2)
    have hb : (bF:ℝ)=b := by simpa [bF,starMatrix] using hm (e.symm 1) (e.symm 2)
    have he : M=(fun i j=>starMatrix aF bF (e i) (e j)) := by
      funext i j
      apply Subtype.ext
      have h:=hm i j
      change (M i j:ℝ)=_ at h ⊢
      rw [h]
      generalize e i=x
      generalize e j=y
      fin_cases x <;> fin_cases y <;> simp [starMatrix,ha,hb]
    rw [he]
    exact color_inFP basis e _ (signed_star_inFP basis aF bF)

end PlanarHom.SignedThreeState

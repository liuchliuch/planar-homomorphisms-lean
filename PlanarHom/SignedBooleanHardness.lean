import PlanarHom.SignedLeafGadgetReduction
import PlanarHom.BiasedBooleanFoundationClosed
import PlanarHom.SignedSmallStateTractability

/-! Complete signed Boolean hardness outside the four literal alternatives.
The finite cofacial leaf gadget is optional; then actual path-square and
thickening programs reduce from the already proved positive biased foundation. -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {F : IntermediateField ℚ ℝ} [FiniteDimensional ℚ F] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ F)

private theorem positive_boolean_field_hard (B : Matrix (Fin 2) (Fin 2) F)
    (hs : ∀i j,B i j=B j i) (hp : ∀i j,0<(B i j:ℝ))
    (hb : B 0 0≠B 1 1) (hd : B 0 0*B 1 1≠B 0 1^2) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>B) emptyUnaries (fun _=>1)) := by
  let C : Matrix Bool Bool F := fun i j=>B (finTwoEquiv.symm i) (finTwoEquiv.symm j)
  have hh := BiasedPositiveHardness.promisedSharpPHard basis F.subtype C
    (fun i j=>hs _ _) (fun i j=>hp _ _) hb hd
  have he := evaluationProblem_colorReindex basis finTwoEquiv (fun _:Fin 1=>C)
    (BiasedPositiveHardness.noUnary Bool) (fun _=>1)
  have hnone : (fun (l:Fin 0) i=>BiasedPositiveHardness.noUnary Bool l (finTwoEquiv i))=
      (emptyUnaries : Fin 0→Fin 2→F) := by funext l; exact l.elim0
  simp only [C,Equiv.symm_apply_apply,hnone] at he
  exact he.symm ▸ hh

private theorem boolean_gram_target_hard (a b c : F)
    (hp : ∀i j,0<gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) i j)
    (hb : gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) 0 0≠gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) 1 1)
    (hd : (gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ)).det≠0) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>booleanMatrix a b c)
      emptyUnaries (fun _=>1)) := by
  let B := schurSquare (booleanMatrix a b c*booleanMatrix a b c)
  have hm : (fun i j=>(B i j:ℝ))=gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) := by
    rw [gramSquareBoolean_eq]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,schurSquare,booleanMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  have hs : ∀i j,B i j=B j i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B,schurSquare,booleanMatrix,Matrix.mul_apply,Fin.sum_univ_two,add_comm,mul_comm]
  have hhard : PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>B) emptyUnaries (fun _=>1)) := by
    apply positive_boolean_field_hard basis B hs
    · intro i j
      change 0<(fun i j=>(B i j:ℝ)) i j
      rw [hm]
      exact hp i j
    · intro h
      apply hb
      have h' := congrArg Subtype.val h
      simpa only [show (B 0 0:ℝ)=gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) 0 0 from congrFun (congrFun hm 0) 0,
        show (B 1 1:ℝ)=gramSquareBoolean (a:ℝ) (b:ℝ) (c:ℝ) 1 1 from congrFun (congrFun hm 1) 1] using h'
    · intro h
      apply hd
      have h' : (B 0 0:ℝ)*(B 1 1:ℝ)=(B 0 1:ℝ)^2 := congrArg Subtype.val h
      have he := congrFun (congrFun hm 0) 0
      have he' := congrFun (congrFun hm 1) 1
      have he'' := congrFun (congrFun hm 0) 1
      rw [he,he',he''] at h'
      rw [gramSquareBoolean,det_booleanMatrix]
      exact sub_eq_zero.mpr h'
  exact hhard.trans (squaredGramReduction basis (booleanMatrix a b c) emptyUnaries)

/-- Exact CM23 signed Boolean hard complement, proved by actual planar
reductions rather than imported as an axiom. -/
theorem signed_boolean_hard (a b c : F) (h : ¬BooleanEasy (a:ℝ) (b:ℝ) (c:ℝ)) :
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>booleanMatrix a b c)
      emptyUnaries (fun _=>1)) := by
  obtain ⟨x,y,z,hform,hp,hb,hd⟩ := signedBoolean_positive_target (a:ℝ) (b:ℝ) (c:ℝ) h
  rcases hform with ⟨rfl,rfl,rfl⟩|hform
  · exact boolean_gram_target_hard basis a b c hp hb hd
  · have hx : x=(a:ℝ)*((a:ℝ)+(b:ℝ))^2 := congrArg Prod.fst hform
    have hy : y=(b:ℝ)*((a:ℝ)+(b:ℝ))*((b:ℝ)+(c:ℝ)) := congrArg (fun p:ℝ×ℝ×ℝ=>p.2.1) hform
    have hz : z=(c:ℝ)*((b:ℝ)+(c:ℝ))^2 := congrArg (fun p:ℝ×ℝ×ℝ=>p.2.2) hform
    rw [hx,hy,hz] at hp hb hd
    have hh := boolean_gram_target_hard basis (a*(a+b)^2) (b*(a+b)*(b+c)) (c*(b+c)^2)
      (by simpa only [IntermediateField.coe_mul,IntermediateField.coe_add,IntermediateField.coe_pow] using hp)
      (by simpa only [IntermediateField.coe_mul,IntermediateField.coe_add,IntermediateField.coe_pow] using hb)
      (by simpa only [IntermediateField.coe_mul,IntermediateField.coe_add,IntermediateField.coe_pow] using hd)
    have hm := leafDecorated_booleanMatrix a b c
    rw [←hm] at hh
    exact hh.trans (leafDecorationReduction basis (booleanMatrix a b c) emptyUnaries)

end PlanarHom.SignedThreeState

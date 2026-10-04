import PlanarHom.BodyUnconditionalClassification
import PlanarHom.WeightedBlockTractabilityConditional
import PlanarHom.RectangularUnweightedSourceCompleteConditional

/-! NEW full weighted tensor and positive rectangular body endpoints. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode Boolean Structures BooleanTensorEasyAssembly
variable {q d : ℕ}

theorem lemma83 (L : RealLanguage q 1 0) (e : Fin q≃Cube d)
    (ρ : Fin d→ℝ) (hρ : ∀r,0<ρ r) (hne : ∀r,ρ r≠1)
    (hM : ∀i j,L.matrices 0 i j=tensor ρ (e i) (e j)) (hw : ∀i,0<L.weights i) :
    ((∀i j,L.weights i=L.weights j) → L.problem.InFP) ∧
    ((∃i j,L.weights i≠L.weights j) → PromisedSharpPHard L.problem) := by
  letI : Nonempty (Fin q):=⟨e.symm (fun _=>false)⟩
  have hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i:=by intro i j; rw [hM,hM,tensor_symm]
  have hp : ∀i j,0<L.matrices 0 i j:=by intro i j; rw [hM]; exact tensor_pos hρ _ _
  have hd : ∀i,L.matrices 0 i i=1:=by intro i; rw [hM,tensor_diag]
  have hi : Function.Injective (L.matrices 0):=by
    intro i j hij
    apply e.injective
    apply tensor_rows_injective hρ hne
    funext x
    have h:=congrFun hij (e.symm x)
    simpa only [hM,e.apply_symm_apply] using h
  refine ⟨?_,PositiveClassMomentRigidity.nonconstant_weights_hard positivePottsFoundation L 0 hs hp hd hi hw⟩
  intro hc
  let chart : Fin q≃Fin 1×Cube d := {
    toFun:=fun i=>(0,e i)
    invFun:=fun p=>e.symm p.2
    left_inv:=fun i=>e.symm_apply_apply i
    right_inv:=by rintro ⟨i,x⟩; have hi:i=0:=Subsingleton.elim _ _; subst i; simp }
  let c:=L.weights (e.symm (fun _=>false))
  have ha : AllowedWeightedBlock (L.matrices 0) L.weights := by
    apply AllowedWeightedBlock.positive 1 d (by decide) (fun _=>1) (fun _=>c) ρ
      (fun _=>zero_lt_one) (fun _=>hw _) (fun r=>⟨hρ r,hne r⟩) chart
    · intro i j
      simpa only [chart,Equiv.coe_fn_mk,one_mul] using hM i j
    · intro i
      exact hc _ _
  have hf:=WeightedBlockTractability.allowedWeightedBlock_inFP_of_ising positiveIsingFoundation
    L.field L.basis (L.matricesK 0) L.weightsK ha
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hm,hu]
  exact hf

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
namespace PlanarHom.Structures

theorem single_block_class {C : Type} [Nonempty C] (M : Matrix C C ℝ) (h : AllowedBlock M) : NonnegativeClass M := by
  refine ⟨1,(fun _=>0),?_,?_,?_⟩
  · intro r
    exact ⟨Classical.choice inferInstance,Subsingleton.elim _ _⟩
  · intro i j hh
    exact (hh rfl).elim
  · intro r
    let e : {c : C // (0:Fin 1)=r}≃C := {
      toFun:=Subtype.val
      invFun:=fun c=>⟨c,Subsingleton.elim _ _⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
    exact h.equiv e

end PlanarHom.Structures
namespace PlanarHom.RectangularUnweightedSourceForms
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage Complexity Structures
open RectangularSourceNormSimulation

theorem theorem91 {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
    (L : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ) (hV : ∀i j,0<V i j)
    (hM : L.matrices 0=block V) (hunit : ∀i,L.weights i=1) :
    (RectangularTensorForm V → L.problem.InFP) ∧
    (¬RectangularTensorForm V → PromisedSharpPHard L.problem) := by
  letI : Nonempty (Fin (p+s)):=⟨Fin.castAdd s (Classical.choice inferInstance)⟩
  refine ⟨?_,?_⟩
  · intro hf
    apply L.nonnegative_class_inFP hunit
    rw [hM]
    exact single_block_class _ (allowedBlock_of_form V hf)
  · intro hbad
    by_contra hn
    exact hbad (source_language_form_of_not_hard_of_potts positivePottsFoundation L V hV
      (fun i j=>congrFun (congrFun hM i) j) hunit hn)

end PlanarHom.RectangularUnweightedSourceForms

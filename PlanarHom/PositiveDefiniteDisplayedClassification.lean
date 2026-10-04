import PlanarHom.BodyUnconditionalClassification

/-! NEW exact displayed factors and complete original Theorem 6.1. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Boolean BooleanTensorEasyAssembly
variable {q : ℕ}

def DisplayedPositiveDefiniteForm (M : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∃d : ℕ,∃e : Fin q≃Cube d,∃γ : ℝ,∃a b : Fin d→ℝ,
    0<γ ∧ (∀r,0<b r ∧ b r<a r) ∧ Matrix.reindex e e M=
      γ • CubeTensorExponential.tensor (fun r i j=>if i=j then a r else b r)

theorem positiveDefiniteForm_iff_displayed (M : Matrix (Fin q) (Fin q) ℝ) :
    PositiveDefiniteTensorForm M ↔ DisplayedPositiveDefiniteForm M := by
  constructor
  · rintro ⟨d,e,γ,ρ,hγ,hρ,he⟩
    exact ⟨d,e,γ,(fun _=>1),ρ,hγ,hρ,he⟩
  · rintro ⟨d,e,γ,a,b,hγ,hab,he⟩
    have ha : ∀r,0<a r:=fun r=>lt_trans (hab r).1 (hab r).2
    have ht : CubeTensorExponential.tensor (fun r i j=>if i=j then a r else b r)=
        (∏r,a r) • tensor (fun r=>b r/a r) := by
      ext x y
      change (∏r,if x r=y r then a r else b r)=(∏r,a r)*(∏r,W (b r/a r) (x r) (y r))
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _
      by_cases h:x r=y r
      · simp [W,h]
      · simp only [W,if_neg h]
        field_simp [ne_of_gt (ha r)]
    refine ⟨d,e,γ*(∏r,a r),(fun r=>b r/a r),mul_pos hγ (Finset.prod_pos (fun r _=>ha r)),?_,?_⟩
    · intro r
      exact ⟨div_pos (hab r).1 (ha r),(div_lt_one (ha r)).mpr (hab r).2⟩
    · rw [he,ht,smul_smul]

theorem positiveDefiniteTensorForm_inFP (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (h : PositiveDefiniteTensorForm (L.matrices 0)) : L.problem.InFP := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,he⟩:=h
  let chart : Fin q≃Fin 1×Cube d := {
    toFun:=fun i=>(0,e i)
    invFun:=fun p=>e.symm p.2
    left_inv:=fun i=>e.symm_apply_apply i
    right_inv:=by rintro ⟨i,x⟩; have hi:i=0:=Subsingleton.elim _ _; subst i; simp }
  apply L.positiveTensorForm_inFP_of_ising positiveIsingFoundation hunit
  refine ⟨1,d,chart,(fun _=>Real.sqrt γ),ρ,by decide,(fun _=>Real.sqrt_pos.mpr hγ),
    (fun r=>(hρ r).1),?_⟩
  ext x y
  have hm:=congrFun (congrFun he x.2) y.2
  simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,chart,Equiv.coe_fn_mk,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Real.mul_self_sqrt hγ.le] using hm

theorem theorem61 (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hnn : ∀i j,0≤L.matrices 0 i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices 0) hpd.1).Connected) :
    (DisplayedPositiveDefiniteForm (L.matrices 0) → L.problem.InFP) ∧
    (¬DisplayedPositiveDefiniteForm (L.matrices 0) → PromisedSharpPHard L.problem) := by
  refine ⟨fun h=>L.positiveDefiniteTensorForm_inFP hunit ((positiveDefiniteForm_iff_displayed _).mpr h),?_⟩
  intro hbad
  by_contra hn
  exact hbad ((positiveDefiniteForm_iff_displayed _).mp
    (L.positiveDefiniteTensorForm_of_not_hard positivePottsFoundation hunit hpd hnn hconn hn))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

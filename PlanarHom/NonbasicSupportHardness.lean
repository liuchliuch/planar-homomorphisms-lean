import PlanarHom.ZeroOneSourceStructure
import PlanarHom.Corollary32Real

/-! NEW original-source numerical support hardness gate. Entrywise support is
obtained by the actual Corollary 3.2 reduction with original positive background
weights. Section 7 is then proved internally via the nonzero row quotient and
integer Gram tensor obstruction; it is not a separate hardness assumption. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode RootedRestriction ZeroOneBasicStructure
variable {q : ℕ}

def numericalSupportLanguage (L : RealLanguage q 1 0) : RealLanguage q 1 0 where
  matrices := fun _ i j=>if L.matrices 0 i j=0 then 0 else 1
  unaries := fun u=>u.elim0
  weights := L.weights
  matrices_algebraic := fun _ i j=>by
    by_cases h : L.matrices 0 i j=0
    · simp only [h,ite_true]; exact isAlgebraic_zero
    · simp only [h,ite_false]; exact isAlgebraic_one
  unaries_algebraic := fun u=>u.elim0
  weights_algebraic := L.weights_algebraic

def numericalSupportSourceReduction (L : RealLanguage q 1 0) :
    PromisePolyTimeTuringReduction L.numericalSupportLanguage.problem L.problem := by
  have first := L.numericalSupportLanguage.presentationDescentReduction L.field L.basis
    (fun _ : Fin 1=>MagnitudeSign.supportMatrix (L.matricesK 0)) L.unariesK L.weightsK
    (fun _ i j=>Corollary32.support_entry_coe L i j) (fun u=>u.elim0) (fun _=>rfl)
  let chain := Corollary32.support_chains L
  exact first.trans (chain.1.some.trans chain.2.1.some)

theorem numerical_support_basic_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀i,0<L.weights i) (hnot : ¬PromisedSharpPHard L.problem) :
    ∀c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      BasicZeroOneComponent (fun i j : c.supp=>if L.matrices 0 i.val j.val=0 then 0 else 1) := by
  let S := L.numericalSupportLanguage
  have hSsymm : ∀i j,S.matrices 0 i j=S.matrices 0 j i := by
    intro i j
    change (if L.matrices 0 i j=0 then (0:ℝ) else 1)=(if L.matrices 0 j i=0 then 0 else 1)
    rw [hs i j]
  have hS01 : ∀i j,S.matrices 0 i j=0 ∨ S.matrices 0 i j=1 := by
    intro i j
    change (if L.matrices 0 i j=0 then (0:ℝ) else 1)=0 ∨ _
    by_cases h : L.matrices 0 i j=0
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  have hnS : ¬PromisedSharpPHard S.problem :=
    fun hh=>hnot (hh.trans L.numericalSupportSourceReduction)
  have hb := S.zeroOne_basic_of_not_hard hPotts hSsymm hw hS01 hnS
  have hg : colorSupport (S.matrices 0) hSsymm=colorSupport (L.matrices 0) hs := by
    ext i j
    change (i≠j ∧ (if L.matrices 0 i j=0 then (0:ℝ) else 1)≠0) ↔ (i≠j ∧ L.matrices 0 i j≠0)
    by_cases h : L.matrices 0 i j=0 <;> simp [h]
  rw [hg] at hb
  exact hb

/-- The contrapositive used by the main dichotomies. -/
theorem numerical_support_nonbasic_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀i,0<L.weights i)
    (hbad : ∃c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      ¬BasicZeroOneComponent (fun i j : c.supp=>if L.matrices 0 i.val j.val=0 then 0 else 1)) :
    PromisedSharpPHard L.problem := by
  by_contra hn
  obtain ⟨c,hc⟩ := hbad
  exact hc (L.numerical_support_basic_of_not_hard hPotts hs hw hn c)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

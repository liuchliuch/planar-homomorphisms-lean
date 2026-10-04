/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.PositiveNormalizedCoreSource
import PlanarHom.PositiveSourceFormsConditional
import PlanarHom.PositiveNormalizationMomentConsequences

/-! Complete literal source8.1 assembly with the one explicit remaining
positive Potts hardness foundation. Normalization, quotient programs, constant
moments and amplitude reconstruction are derived from the original source. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity
variable {q bt ut : ℕ} [Nonempty (Fin q)]

theorem positiveTensorForm_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀ i j,0<L.matrices old i j) (hnot : ¬PromisedSharpPHard L.problem) :
    PositiveTensorForm (L.matrices old) := by
  obtain ⟨d,eQ,ρ,hρ,hcore⟩ := L.normalized_quotient_tensor_of_not_hard hPotts old hs hpos
    (fun i=>by rw [hunit]; exact zero_lt_one) hnot
  have hm := L.normalized_moments_constant hPotts old hs hpos hunit hnot
  exact positiveTensorForm_of_quotient_data (L.matrices old) hpos hs (fun r s m=>hm m r s)
    d eQ ρ (fun r=>(hρ r).1) hcore

/-- Original positive real-algebraic source, exact displayed rank-one/tensor
criterion, original finite-field answer codec, and actual FP/hardness machines. -/
theorem theorem81_of_potts_ising (hPotts : PositivePottsFoundation)
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpos : ∀ i j,0<L.matrices 0 i j) :
    (PositiveTensorForm (L.matrices 0) → L.problem.InFP) ∧
      (¬PositiveTensorForm (L.matrices 0) → PromisedSharpPHard L.problem) := by
  refine ⟨L.positiveTensorForm_inFP_of_ising hIsing hunit,?_⟩
  intro hbad
  by_contra hnot
  exact hbad (L.positiveTensorForm_of_not_hard hPotts 0 hunit hs hpos hnot)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

import PlanarHom.RectangularDegreeTwoForcing
import PlanarHom.RectangularHigherDegreeRigidity

/-! NEW complete induction fixing all Fourier degrees after the genuine
singleton signed permutation has been forced by the physical norm equality. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem all_degree_permutation (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hθ:∀i,0<θ i) (hO:O*O.transpose=1)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hdeg:∀S T,Boolean.degree S≠Boolean.degree T→O S T=0)
    (h00:O (fun _=>false) (fun _=>false)=1)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hnorm:∀S,(∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(characterWeight θ S)^2):
    ∃p:Fin d≃Fin d,∃flip:Fin d→Bool,∀S T,O S T=permutationRow p flip S T:=by
  obtain ⟨p,flip,hsingle⟩:=singleton_signed_permutation_of_norms C O θ hθ hO hrep hdeg hrow hnorm
  refine ⟨p,flip,?_⟩
  have hall:∀r:ℕ,∀S:Cube d,Boolean.degree S=r→∀T:Cube d,O S T=permutationRow p flip S T:=by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih=>
      intro S hS T
      by_cases hr0:r=0
      · have hS0:Boolean.degree S=0:=hS.trans hr0
        have hs:S=(fun _=>false):=(degree_zero_iff S).mp hS0
        subst S
        by_cases ht:T=(fun _=>false)
        · subst T
          simpa only [permutationRow,permuteIndex_zero,if_true,character_zero] using h00
        · have hT:Boolean.degree T≠0:=fun h=>ht ((degree_zero_iff T).mp h)
          rw [hdeg _ T (by simpa [Boolean.degree] using hT.symm)]
          simp only [permutationRow,permuteIndex_zero,ht,if_false]
      · by_cases hr1:r=1
        · have hS1:Boolean.degree S=1:=hS.trans hr1
          obtain ⟨i,hi⟩:=(degree_one_iff S).mp hS1
          subst S
          by_cases ht:Boolean.degree T=1
          · obtain ⟨j,hj⟩:=(degree_one_iff T).mp ht
            subst T
            exact (hsingle i j).trans (permutationRow_singleton p flip i j).symm
          · have hd:Boolean.degree (unitBit i)≠Boolean.degree T:=by rw [degree_unitBit];exact Ne.symm ht
            rw [hdeg _ _ hd,permutationRow_degree p flip _ _ hd]
        · exact higher_row_eq_from_lower C O θ hθ hO hrep hrow hnorm p flip S (by omega)
            (fun I hI J=>ih (Boolean.degree I) (by omega) I rfl J) T
  exact fun S T=>hall (Boolean.degree S) S rfl T

end PlanarHom.RectangularWalshConvolution

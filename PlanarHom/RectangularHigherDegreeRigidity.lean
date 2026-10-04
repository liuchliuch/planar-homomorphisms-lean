import PlanarHom.RectangularCharacterPermutation
import PlanarHom.RectangularSplitWeights
import PlanarHom.RectangularNormRigidity
import PlanarHom.RectangularSourceNormData

/-! NEW actual higher-degree rigidity from the source-derived polynomial norm
identity. All lower-degree subset contributions are counted explicitly. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem proper_split_permutation (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (p:Fin d≃Fin d) (flip:Fin d→Bool) (S T:Cube d)
    (hlow:∀I,Boolean.degree I<Boolean.degree S→∀J,O I J=permutationRow p flip I J)
    (A:Finset (Fin d)) (hA:A⊆bitSupport S) (hne:A≠∅) (hproper:A≠bitSupport S):
    splitConvolution C S T (bitsOfSet A)=characterWeight θ S*permutationRow p flip S T:=by
  obtain ⟨hI,hJ⟩:=proper_split_degrees S A hA hne hproper
  have hsub:bitSupport (bitsOfSet A)⊆bitSupport S:=by simpa only [support_bitsOfSet] using hA
  have hx:xor (bitsOfSet A) (xor S (bitsOfSet A))=S:=by
    funext i
    simp [Boolean.xor,Bool.xor_comm,Bool.xor_left_comm]
  calc
    _ = (characterWeight θ (bitsOfSet A)*characterWeight θ (xor S (bitsOfSet A)))*
        rowConvolution (permutationRow p flip (bitsOfSet A)) (permutationRow p flip (xor S (bitsOfSet A))) T:=by
      unfold splitConvolution rowConvolution
      simp_rw [hrep,hlow _ hI,hlow _ hJ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring
    _ = _:=by rw [characterWeight_split θ S _ hsub,permutationRow_convolution,hx]

theorem leading_coefficient_from_lower (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (p:Fin d≃Fin d) (flip:Fin d→Bool) (S T:Cube d) (hS:0<Boolean.degree S)
    (hlow:∀I,Boolean.degree I<Boolean.degree S→∀J,O I J=permutationRow p flip I J):
    (squareCoefficientPolynomial C S T).coeff (Boolean.degree S)=
      characterWeight θ S*(2*O S T+((2:ℝ)^(Boolean.degree S)-2)*permutationRow p flip S T):=by
  rw [squareCoefficient_subsets]
  have hs:(bitSupport S).Nonempty:=Finset.card_pos.mp (by simpa only [degree_eq_support_card] using hS)
  trans ∑A∈(bitSupport S).powerset,
    if A=∅ then characterWeight θ S*O S T else
      if A=bitSupport S then characterWeight θ S*O S T else characterWeight θ S*permutationRow p flip S T
  · apply Finset.sum_congr rfl
    intro A hA
    by_cases h0:A=∅
    · subst A
      simp only [bitsOfSet_empty,split_empty C hrow,ite_true,hrep]
    · by_cases he:A=bitSupport S
      · subst A
        simp only [bitsOfSet_support,split_self C hrow,hrep,ite_true,h0,if_false]
      · simp only [h0,if_false,he]
        exact proper_split_permutation C O θ hrep p flip S T hlow A (Finset.mem_powerset.mp hA) h0 he
  · rw [sum_powerset_boundary _ hs,←degree_eq_support_card]
    ring

theorem higher_row_eq_from_lower (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hθ:∀i,0<θ i) (hO:O*O.transpose=1)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hnorm:∀S,(∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(characterWeight θ S)^2)
    (p:Fin d≃Fin d) (flip:Fin d→Bool) (S:Cube d) (hS:2≤Boolean.degree S)
    (hlow:∀I,Boolean.degree I<Boolean.degree S→∀J,O I J=permutationRow p flip I J):
    ∀T,O S T=permutationRow p flip S T:=by
  let a:ℝ:=(2:ℝ)^(Boolean.degree S)-2
  have ha:0<a:=by
    have hp: (2:ℝ)^2≤(2:ℝ)^(Boolean.degree S):=pow_le_pow_right₀ (by norm_num) hS
    dsimp [a]
    norm_num at hp
    linarith
  have hw:0<characterWeight θ S:=Finset.prod_pos (fun i _=>hθ i)
  have heq:(∑T:Cube d,(2*O S T+a*permutationRow p flip S T)^2)=(2+a)^2:=by
    have he:=hnorm S
    simp_rw [leading_coefficient_from_lower C O θ hrep hrow p flip S _ (by omega) hlow,mul_pow] at he
    rw [←Finset.mul_sum] at he
    apply mul_left_cancel₀ (pow_ne_zero 2 hw.ne')
    calc
      _=4^(Boolean.degree S)*(characterWeight θ S)^2:=he
      _=_:=by
        have hp:(4:ℝ)^(Boolean.degree S)=((2:ℝ)^(Boolean.degree S))^2:=by
          rw [pow_two,←mul_pow]
          norm_num
        rw [hp]
        dsimp [a]
        ring
  have h:=norm_equality_forces_equal (O S) (permutationRow p flip S) a ha
    (orthogonal_row_norm O hO S) (permutationRow_norm p flip S) heq
  exact fun T=>congrFun h T

end PlanarHom.RectangularWalshConvolution

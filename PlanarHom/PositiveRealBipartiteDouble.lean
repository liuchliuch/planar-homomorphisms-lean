import PlanarHom.PositiveRealBipartiteMatrix
import PlanarHom.PositiveKernelScalingRigidity

/-! NEW exact numerical obstruction for nonconstant positive weights on the
two sides of an Ising tensor. Strict positive-kernel scaling rigidity proves
the obstruction; the original invertible tensor supplies both actual PD Grams. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveRealCore
open Boolean
variable {I : Type} [Fintype I] [DecidableEq I]

def scaledTensor {d : ℕ} (c : ℝ) (ρ : Fin d → ℝ) : Matrix (Cube d) (Cube d) ℝ := c • tensor ρ

theorem scaledTensor_det_ne_zero {d : ℕ} (c : ℝ) (hc : 0<c) (ρ : Fin d → ℝ)
    (hρ : ∀r,0<ρ r) (hne : ∀r,ρ r≠1) : (scaledTensor c ρ).det≠0 := by
  have hu := (tensor_isUnit_iff_of_pos hρ).mpr hne
  have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [scaledTensor,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc.ne') hd

theorem decorated_positive (B : Matrix I I ℝ) (hp : ∀i j,0<B i j)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) :
    ∀i j,0<decorated B μ ν i j := by
  intro i j
  rw [decorated_entry]
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr (hμ i)) (hp i j)) (Real.sqrt_pos.mpr (hν j))

theorem leftGram_positive [Nonempty I] (B : Matrix I I ℝ) (hp : ∀i j,0<B i j)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) :
    ∀i j,0<leftGram B μ ν i j := by
  intro i j
  exact Finset.sum_pos (fun k _=>mul_pos (decorated_positive B hp μ ν hμ hν i k)
    (decorated_positive B hp μ ν hμ hν j k)) Finset.univ_nonempty

theorem rightGram_positive [Nonempty I] (B : Matrix I I ℝ) (hp : ∀i j,0<B i j)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) :
    ∀i j,0<rightGram B μ ν i j := by
  intro i j
  exact Finset.sum_pos (fun k _=>mul_pos (decorated_positive B hp μ ν hμ hν k i)
    (decorated_positive B hp μ ν hμ hν k j)) Finset.univ_nonempty

theorem scaledTensor_square_row_sum {d : ℕ} (c : ℝ) (ρ : Fin d → ℝ) (i : Cube d) :
    (∑j,(scaledTensor c ρ i j)^2)=c^2*∏r,(1+ρ r^2) := by
  change (∑j,(c*tensor ρ i j)^2)=_
  simp_rw [mul_pow,←tensor_pow]
  rw [←Finset.mul_sum,tensor_row_sum]

theorem bipartite_ising_core {d : ℕ} (c : ℝ) (hc : 0<c) (ρ : Fin d → ℝ)
    (hρ : ∀r,0<ρ r) (hne : ∀r,ρ r≠1)
    (μ ν : Cube d → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i)
    (hnon : (∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j)) :
    (leftGram (scaledTensor c ρ) μ ν).PosDef ∧
    (rightGram (scaledTensor c ρ) μ ν).PosDef ∧
    (∀i j,0<leftGram (scaledTensor c ρ) μ ν i j) ∧
    (∀i j,0<rightGram (scaledTensor c ρ) μ ν i j) ∧
    ((∃i j,leftGram (scaledTensor c ρ) μ ν i i≠leftGram (scaledTensor c ρ) μ ν j j) ∨
      (∃i j,rightGram (scaledTensor c ρ) μ ν i i≠rightGram (scaledTensor c ρ) μ ν j j)) := by
  let B := scaledTensor c ρ
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (scaledTensor_det_ne_zero c hc ρ hρ hne))
  have hpos : ∀i j,0<B i j := fun i j=>mul_pos hc (tensor_pos hρ i j)
  refine ⟨leftGram_posDef B hB μ ν hμ hν,rightGram_posDef B hB μ ν hμ hν,
    leftGram_positive B hpos μ ν hμ hν,rightGram_positive B hpos μ ν hμ hν,?_⟩
  by_contra hnone
  have hleft : ∀i j,leftGram B μ ν i i=leftGram B μ ν j j := by
    have hh : ¬∃i j,leftGram B μ ν i i≠leftGram B μ ν j j := fun h=>hnone (.inl h)
    simpa only [not_exists,not_not] using hh
  have hright : ∀i j,rightGram B μ ν i i=rightGram B μ ν j j := by
    have hh : ¬∃i j,rightGram B μ ν i i≠rightGram B μ ν j j := fun h=>hnone (.inr h)
    simpa only [not_exists,not_not] using hh
  let R := c^2*∏r,(1+ρ r^2)
  have hR : 0<R := mul_pos (sq_pos_of_pos hc)
    (Finset.prod_pos (fun r _=>by positivity))
  have hrow : ∀i,∑j,B i j^2=R := scaledTensor_square_row_sum c ρ
  have hcol : ∀j,∑i,B i j^2=R := by
    intro j
    calc
      (∑i,B i j^2) = ∑i,B j i^2 := by
        apply Finset.sum_congr rfl
        intro i _
        change (c*tensor ρ i j)^2=(c*tensor ρ j i)^2
        rw [tensor_symm]
      _ = R := hrow j
  let z : Cube d := fun _=>false
  have hconstant := PositiveKernelScalingRigidity.constant_scalings
    (fun i j=>B i j^2) (fun i j=>sq_pos_of_pos (hpos i j)) R hR hrow hcol μ ν hμ hν
    (leftGram B μ ν z z) (rightGram B μ ν z z)
    (fun i=>(leftGram_diagonal B μ ν (fun i=>(hμ i).le) (fun i=>(hν i).le) i).symm.trans (hleft i z))
    (fun j=>(rightGram_diagonal B μ ν (fun i=>(hμ i).le) (fun i=>(hν i).le) j).symm.trans (hright j z))
  rcases hnon with ⟨i,j,hij⟩|⟨i,j,hij⟩
  · exact hij (hconstant.1 i j)
  · exact hij (hconstant.2 i j)

end PlanarHom.PositiveRealCore

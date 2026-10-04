import PlanarHom.PositiveRealBipartiteDouble
import PlanarHom.WeightRigidity

/-! Exact real numerical content of A.10/A.11. Complexity conclusions require
actual A.8 decorated-Gram reductions and A.6 hardness, tracked separately. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealCoreObstructions
open Boolean PositiveRealCore
variable {d:ℕ}

theorem symmetric_square_eq_leftGram {I:Type} [Fintype I] [DecidableEq I]
    (B:Matrix I I ℝ) (hs:∀i j,B i j=B j i) (u:I→ℝ) :
    (decorated B u u)^2=leftGram B u u := by
  have ht:(decorated B u u).transpose=decorated B u u := by
    ext i j
    simp only [Matrix.transpose_apply,decorated_entry]
    rw [hs j i]
    ring
  rw [leftGram,ht,pow_two]

theorem symmetric_regular_core {I:Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (B:Matrix I I ℝ) (hs:∀i j,B i j=B j i) (hB:IsUnit B) (hp:∀i j,0<B i j)
    (r:ℝ) (hr:∀i,∑j,B i j^2=r) (u:I→ℝ) (hu:∀i,0<u i) (hnon:∃i j,u i≠u j) :
    ((decorated B u u)^2).PosDef ∧ (∀i j,0<((decorated B u u)^2) i j) ∧
      (∃i j,((decorated B u u)^2) i i≠((decorated B u u)^2) j j) := by
  rw [symmetric_square_eq_leftGram B hs u]
  refine ⟨leftGram_posDef B hB u u hu hu,leftGram_positive B hp u u hu hu,?_⟩
  obtain ⟨i,j,hij⟩:=WeightRigidity.weighted_diagonal_nonconstant (fun i j=>B i j^2) u r
    (fun i j=>sq_pos_of_pos (hp i j)) hr hu hnon
  exact ⟨i,j,by simpa only [leftGram_diagonal B u u (fun i=>(hu i).le) (fun i=>(hu i).le)] using hij⟩

theorem symmetric_core (ρ:Fin d→ℝ) (hρ:∀j,0<ρ j) (hne:∀j,ρ j≠1)
    (u:Cube d→ℝ) (hu:∀i,0<u i) (hnon:∃i j,u i≠u j) :
    (leftGram (Boolean.tensor ρ) u u).PosDef ∧
    (∀i j,0<leftGram (Boolean.tensor ρ) u u i j) ∧
    (∃i j,leftGram (Boolean.tensor ρ) u u i i≠leftGram (Boolean.tensor ρ) u u j j) := by
  have hB:IsUnit (show Matrix (Cube d) (Cube d) ℝ from Boolean.tensor ρ):=(Boolean.tensor_isUnit_iff_of_pos hρ).mpr hne
  refine ⟨leftGram_posDef _ hB u u hu hu,leftGram_positive _ (tensor_pos hρ) u u hu hu,?_⟩
  obtain ⟨i,j,hij⟩:=WeightRigidity.weighted_diagonal_nonconstant
    (fun i j=>(Boolean.tensor ρ i j)^2) u (∏r,(1+(ρ r)^2))
    (fun i j=>sq_pos_of_pos (tensor_pos hρ i j))
    (fun i=>by simpa only [←tensor_pow] using tensor_row_sum (fun r=>(ρ r)^2) i) hu hnon
  exact ⟨i,j,by simpa only [leftGram_diagonal _ _ _ (fun i=>(hu i).le) (fun i=>(hu i).le)] using hij⟩

theorem symmetric_core_square (ρ:Fin d→ℝ) (u:Cube d→ℝ) :
    leftGram (Boolean.tensor ρ) u u=(decorated (Boolean.tensor ρ) u u)^2 := by
  have hs:(decorated (Boolean.tensor ρ) u u).transpose=decorated (Boolean.tensor ρ) u u := by
    ext i j
    simp only [Matrix.transpose_apply,decorated_entry]
    rw [tensor_symm ρ j i]
    ring
  rw [leftGram,hs,pow_two]

/-- The two side constants remain independent throughout the statement. -/
theorem bipartite_core (c:ℝ) (hc:0<c) (ρ:Fin d→ℝ) (hρ:∀j,0<ρ j) (hne:∀j,ρ j≠1)
    (μ ν:Cube d→ℝ) (hμ:∀i,0<μ i) (hν:∀j,0<ν j)
    (hnon:(∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j)) :
    (leftGram (scaledTensor c ρ) μ ν).PosDef ∧
    (rightGram (scaledTensor c ρ) μ ν).PosDef ∧
    (∀i j,0<leftGram (scaledTensor c ρ) μ ν i j) ∧
    (∀i j,0<rightGram (scaledTensor c ρ) μ ν i j) ∧
    ((∃i j,leftGram (scaledTensor c ρ) μ ν i i≠leftGram (scaledTensor c ρ) μ ν j j) ∨
      (∃i j,rightGram (scaledTensor c ρ) μ ν i i≠rightGram (scaledTensor c ρ) μ ν j j)) :=
  bipartite_ising_core c hc ρ hρ hne μ ν hμ hν hnon

end PlanarHom.FixedRealCoreObstructions

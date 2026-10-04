import PlanarHom.BooleanMatrix
import PlanarHom.BooleanLogPositivity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! NEW genuine entrywise positive roots of Boolean Gram tensors and equality
of their two cube dimensions. No invertibility or dimension equality is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularGramRoots
variable {a b d:ℕ}

def rootParameters (ρ:Fin d→ℝ) (h:ℕ) : Fin d→ℝ := fun i=>(ρ i)^((h:ℝ)⁻¹)

theorem root_range (ρ:Fin d→ℝ) (hρ:∀i,0<ρ i ∧ ρ i<1) (h:ℕ) (hh:h≠0) :
    ∀i,0<rootParameters ρ h i ∧ rootParameters ρ h i<1 := by
  intro i
  exact ⟨Real.rpow_pos_of_pos (hρ i).1 _,Real.rpow_lt_one (hρ i).1.le (hρ i).2
    (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hh))⟩

theorem positive_tensor_root (C:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (hC:∀i j,0<C i j) (h:ℕ) (hh:h≠0) (γ:ℝ) (ρ:Fin d→ℝ)
    (hρ:∀i,0<ρ i ∧ ρ i<1)
    (he:∀i j,(C i j)^h=γ*Boolean.tensor ρ i j) :
    ∀i j,C i j=γ^((h:ℝ)⁻¹)*Boolean.tensor (rootParameters ρ h) i j := by
  have hγ:0<γ:=by
    have he0:=he (fun _=>false) (fun _=>false)
    rw [Boolean.tensor_diag,mul_one] at he0
    exact he0 ▸ pow_pos (hC _ _) h
  intro i j
  have hp:0<γ^((h:ℝ)⁻¹)*Boolean.tensor (rootParameters ρ h) i j:=
    mul_pos (Real.rpow_pos_of_pos hγ _) (Boolean.tensor_pos (fun r=>(root_range ρ hρ h hh r).1) i j)
  apply (pow_left_inj₀ (hC i j).le hp.le hh).mp
  rw [he,mul_pow,Real.rpow_inv_natCast_pow hγ.le hh,←Boolean.tensor_pow]
  congr 2
  funext r
  exact (Real.rpow_inv_natCast_pow (hρ r).1.le hh).symm

theorem positive_left_gram (B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ)
    (hB:∀i j,0<B i j) : ∀i j,0<(B*B.transpose) i j := by
  intro i j
  exact Finset.sum_pos (fun k _=>mul_pos (hB i k) (hB j k)) Finset.univ_nonempty

theorem tensor_root_posDef (C:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (hC:∀i j,0<C i j) (h:ℕ) (hh:h≠0) (γ:ℝ) (ρ:Fin d→ℝ)
    (hρ:∀i,0<ρ i ∧ ρ i<1)
    (he:∀i j,(C i j)^h=γ*Boolean.tensor ρ i j) : C.PosDef := by
  have hγ:0<γ:=by
    have he0:=he (fun _=>false) (fun _=>false)
    rw [Boolean.tensor_diag,mul_one] at he0
    exact he0 ▸ pow_pos (hC _ _) h
  have hc:C=γ^((h:ℝ)⁻¹) • Boolean.tensor (rootParameters ρ h):=by
    funext i j
    exact positive_tensor_root C hC h hh γ ρ hρ he i j
  rw [hc]
  exact (Boolean.tensor_posDef (fun r=>(root_range ρ hρ h hh r).1)
    (fun r=>(root_range ρ hρ h hh r).2)).smul (Real.rpow_pos_of_pos hγ _)

theorem cube_dimensions_of_tensor_powers
    (B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (hB:∀i j,0<B i j)
    (h k:ℕ) (hh:h≠0) (hk:k≠0) (γX γY:ℝ) (ρX:Fin a→ℝ) (ρY:Fin b→ℝ)
    (hρX:∀i,0<ρX i ∧ ρX i<1) (hρY:∀i,0<ρY i ∧ ρY i<1)
    (hX:∀i j,((B*B.transpose) i j)^h=γX*Boolean.tensor ρX i j)
    (hY:∀i j,((B.transpose*B) i j)^k=γY*Boolean.tensor ρY i j) : a=b := by
  have hpdX:=tensor_root_posDef _ (positive_left_gram B hB) h hh γX ρX hρX hX
  have hpY:∀i j,0<(B.transpose*B) i j:=by
    simpa only [Matrix.transpose_transpose] using positive_left_gram B.transpose (fun i j=>hB j i)
  have hpdY:=tensor_root_posDef _ hpY k hk γY ρY hρY hY
  have hcard:Fintype.card (Boolean.Cube a)=Fintype.card (Boolean.Cube b):=by
    rw [←Matrix.rank_of_isUnit _ hpdX.isUnit,←Matrix.rank_of_isUnit _ hpdY.isUnit,
      Matrix.rank_self_mul_transpose,Matrix.rank_transpose_mul_self]
  apply Nat.pow_right_injective (by decide : 2≤2)
  simpa only [Boolean.Cube,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hcard

end PlanarHom.RectangularGramRoots

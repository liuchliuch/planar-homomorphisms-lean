import PlanarHom.TractableBlockFormsDefinition
import PlanarHom.MainStructuralSupportTransport

/-! NEW direct constructor transport between the exact source structural
predicate and the displayed block forms. No complexity hypothesis is used. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.PositiveRealCore
open Structures TractableBlockComposition
variable {C D : Type}

theorem allowedBlock_pullback (M : Matrix C C ℝ) (h : AllowedBlock M) (e : D ≃ C) :
    AllowedBlock (fun i j=>M (e i) (e j)) := h.equiv e

theorem allowedBlock_form (M : Matrix C C ℝ) (h : AllowedBlock M) : Form M := by
  cases h with
  | zero e hz =>
    exact .zero (e.trans (Equiv.ofUnique Unit (Fin 1))) (funext (fun i=>funext (hz i)))
  | positive k d hk a ρ ha hρ e hm =>
    refine .rankOne ⟨0,hk⟩ e a ha ρ hρ ?_
    ext i j
    simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.apply_symm_apply] using hm (e.symm i) (e.symm j)
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    refine .bipartite ⟨0,hk⟩ ⟨0,hl⟩ e a ha b hb ρ hρ ?_
    ext i j
    have h := hm (e.symm i) (e.symm j)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.apply_symm_apply] at h ⊢
    rw [h]
    change bipartiteAmplitude a b i.1 j.1 * Boolean.tensor ρ i.2 j.2 =
      BipartiteRankTwoTractability.matrix a b i.1 j.1 * Boolean.tensor ρ i.2 j.2
    congr 1

end PlanarHom.PositiveRealCore

import PlanarHom.CenteredLogTensorRank

/-! Literal centered entrywise-log rank in the original finite color chart. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CenteredLogTensorExpansion
open Boolean
variable {q d : ℕ}

def sourceOnes (q : ℕ) : Matrix (Fin q) (Fin q) ℝ := fun _ _=>1
def sourceCentering (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  (1 : Matrix (Fin q) (Fin q) ℝ)-(q:ℝ)⁻¹ • sourceOnes q
def entrywiseLog (M : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j=>Real.log (M i j)

theorem reindex_product (e : Fin q≃Cube d) (A B : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.reindex e e (A*B)=Matrix.reindex e e A*Matrix.reindex e e B := by
  ext x y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply]
  apply Fintype.sum_equiv e
  intro i
  simp only [Equiv.symm_apply_apply]

theorem sourceCentering_reindex (e : Fin q≃Cube d) :
    Matrix.reindex e e (sourceCentering q)=centering d := by
  have hn : q=2^d := by simpa [Cube,Fintype.card_fun] using Fintype.card_congr e
  ext x y
  simp [sourceCentering,sourceOnes,centering,ones,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.one_apply,e.symm.injective.eq_iff,hn]

/-- Original12.4 rank identity; all matrices here use the original q colors. -/
theorem source_centered_log_rank (M : Matrix (Fin q) (Fin q) ℝ)
    (e : Fin q≃Cube d) (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ)
    (hρ : ∀ r,0<ρ r) (hne : ∀ r,ρ r≠1)
    (hM : ∀ i j,M i j=γ*tensor ρ (e i) (e j)) :
    (sourceCentering q*entrywiseLog M*sourceCentering q).rank=d := by
  have hl : Matrix.reindex e e (entrywiseLog M)=tensorLog γ ρ := by
    ext x y
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,entrywiseLog,hM,
      Equiv.apply_symm_apply,tensorLog]
  calc
    (sourceCentering q*entrywiseLog M*sourceCentering q).rank=
        (Matrix.reindex e e (sourceCentering q*entrywiseLog M*sourceCentering q)).rank :=
      (Matrix.rank_reindex e e _).symm
    _=d := by
      rw [reindex_product,reindex_product,sourceCentering_reindex,hl]
      exact centered_entrywise_log_rank γ hγ ρ hρ hne

end PlanarHom.CenteredLogTensorExpansion

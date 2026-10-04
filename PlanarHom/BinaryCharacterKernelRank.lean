import PlanarHom.BinaryLinearCharacters

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BinaryCharacters
variable {X:Type} [AddCommGroup X] [Module F₂ X] [Fintype X] {m:ℕ}

def columns (l:Fin m→X→ₗ[F₂]F₂) : Matrix X (Fin m) ℝ := fun x r=>character (l r) x
def kernel (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) : Matrix X X ℝ :=
  fun x y=>∑r,J r*character (l r) x*character (l r) y

def ones (X:Type) : Matrix X X ℝ := fun _ _=>1

def centering (X:Type) [Fintype X] : Matrix X X ℝ :=
  (1:Matrix X X ℝ)-(Fintype.card X:ℝ)⁻¹ • ones X

theorem columns_gram (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l) :
    (columns l).transpose*columns l=(Fintype.card X:ℝ) • (1:Matrix (Fin m) (Fin m) ℝ) := by
  ext r s
  simp only [Matrix.mul_apply,Matrix.transpose_apply,columns,character_orthogonality,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  by_cases h:r=s <;> simp [h,hl.eq_iff]

def leftInverse (l:Fin m→X→ₗ[F₂]F₂) : Matrix (Fin m) X ℝ :=
  (Fintype.card X:ℝ)⁻¹ • (columns l).transpose

theorem columns_left_inverse (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l) :
    leftInverse l*columns l=1 := by
  rw [leftInverse,Matrix.smul_mul,columns_gram l hl,smul_smul]
  simp [ne_of_gt (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card X:ℝ))]

theorem kernel_factorization (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) :
    kernel l J=columns l*Matrix.diagonal J*(columns l).transpose := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,columns,kernel]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem kernel_rank (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) : (kernel l J).rank=m := by
  rw [kernel_factorization]
  have hleft:=columns_left_inverse l hl
  have hright:(columns l).transpose*(leftInverse l).transpose=1 := by
    have h:=congrArg Matrix.transpose hleft
    simpa only [Matrix.transpose_mul,Matrix.transpose_one] using h
  have hrecover:leftInverse l*(columns l*Matrix.diagonal J*(columns l).transpose)*(leftInverse l).transpose=
      Matrix.diagonal J := by
    calc
      _=(leftInverse l*columns l)*Matrix.diagonal J*((columns l).transpose*(leftInverse l).transpose) := by
        simp only [Matrix.mul_assoc]
      _=Matrix.diagonal J := by rw [hleft,hright,Matrix.one_mul,Matrix.mul_one]
  have hd:(Matrix.diagonal J).rank=m:=by simp [Matrix.rank_diagonal,hJ]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (columns l)))
  · calc
      m=(Matrix.diagonal J).rank:=hd.symm
      _=(leftInverse l*(columns l*Matrix.diagonal J*(columns l).transpose)*(leftInverse l).transpose).rank:=
        congrArg Matrix.rank hrecover.symm
      _≤_ := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem centering_columns (l:Fin m→X→ₗ[F₂]F₂) (hn:∀r,l r≠0) :
    centering X*columns l=columns l := by
  have hz:ones X*columns l=0 := by
    ext x r
    simpa [Matrix.mul_apply,columns,ones] using character_sum_zero (l r) (hn r)
  rw [centering,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,hz,smul_zero,sub_zero]

theorem centering_transpose (X:Type) [Fintype X] : (centering X).transpose=centering X := by
  ext x y
  simp [centering,ones,Matrix.one_apply,eq_comm]

theorem kernel_centered (l:Fin m→X→ₗ[F₂]F₂) (hn:∀r,l r≠0) (J:Fin m→ℝ) :
    centering X*kernel l J*centering X=kernel l J := by
  have hx:=centering_columns l hn
  have hy:(columns l).transpose*centering X=(columns l).transpose := by
    have h:=congrArg Matrix.transpose hx
    simpa only [Matrix.transpose_mul,centering_transpose] using h
  rw [kernel_factorization]
  calc
    _=(centering X*columns l)*Matrix.diagonal J*((columns l).transpose*centering X) := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [hx,hy]

theorem centered_kernel_rank (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (hn:∀r,l r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0) :
    (centering X*kernel l J*centering X).rank=m := by
  rw [kernel_centered l hn]
  exact kernel_rank l hl J hJ

end PlanarHom.BinaryCharacters

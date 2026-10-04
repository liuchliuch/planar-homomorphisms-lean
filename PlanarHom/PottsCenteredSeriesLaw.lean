import PlanarHom.PottsCenteredPathAlgebra
import PlanarHom.SelectedStretchSemantics

/-! NEW reconstruction: the centered matrix has an exact series law. Combined
with the existing actual selected-stretch semantics, long-path filtering can
be performed by coefficient exponents instead of an assumed path-state rule. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered

def entryMatrix (q : ℕ) (x : ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  Matrix.of (fun i j => 1+x*interaction q i j)

@[simp] theorem entryMatrix_apply (q : ℕ) (x : ℚ) (i j : Fin q) :
    entryMatrix q x i j=1+x*interaction q i j := rfl

theorem interaction_colSum (q : ℕ) (j : Fin q) : (∑ i : Fin q,interaction q i j)=0 := by
  calc
    _ = ∑ i : Fin q,interaction q j i := Finset.sum_congr rfl (fun i _ => interaction_symmetric q i j)
    _ = _ := interaction_rowSum q j

/-- Literal matrix multiplication, with both row-sum cancellations explicit. -/
theorem entryMatrix_mul (q : ℕ) (x y : ℚ) :
    entryMatrix q x*entryMatrix q y=(q:ℚ) • entryMatrix q (x*y) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [entryMatrix_apply,Matrix.smul_apply,smul_eq_mul]
  have he (c : Fin q) : (1+x*interaction q i c)*(1+y*interaction q c j)=
      1+x*interaction q i c+y*interaction q c j+(x*y)*(interaction q i c*interaction q c j) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,interaction_rowSum,interaction_colSum,
    interaction_comp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  ring

/-- Every positive-length path has exactly this transfer matrix, including
zero/signed parameters and coincident endpoint colors. -/
theorem entryMatrix_pow (q n : ℕ) (x : ℚ) :
    (entryMatrix q x)^(n+1)=(q:ℚ)^n • entryMatrix q (x^(n+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ _ (n+1),ih,smul_mul_assoc,entryMatrix_mul,smul_smul]
    simp [pow_succ]

/-- Directly connected to the existing genuine private-path color sum. -/
theorem path_sum (q n : ℕ) (x : ℚ) (i j : Fin q) :
    (∑ σ : Fin n → Fin q,PathPower.weight n (entryMatrix q x) i j σ)=
      (q:ℚ)^n*entryMatrix q (x^(n+1)) i j := by
  rw [PathPower.sum_weight,entryMatrix_pow]
  rfl
end PlanarHom.PottsCentered

import PlanarHom.HammingKernelTensor

/-! NEW literal two-edge clique kernels. The two scalar polynomials distinguish
clique sizes in the common-chart source interpolation. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace PlanarHom.HammingKernelTensor

/-- Exact delta-plus-constant presentation, with no sign restriction on t. -/
theorem cliqueKernel_eq_delta {A : Type*} (t : ℝ) (i j : A) :
    cliqueKernel t i j = (if i = j then 1-t else 0) + t := by
  by_cases h : i=j <;> simp [cliqueKernel,h]

/-- Literal middle-color sum, including all possible degenerate color sets. -/
theorem cliqueKernel_square {A : Type*} [Fintype A] (t : ℝ) (i j : A) :
    ((cliqueKernel t : Matrix A A ℝ) * (cliqueKernel t : Matrix A A ℝ)) i j =
      (if i=j then (1-t)^2 else 0) + 2*t*(1-t) + Fintype.card A*t^2 := by
  rw [Matrix.mul_apply]
  simp_rw [cliqueKernel_eq_delta, add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  simp [Finset.sum_mul, Finset.mul_sum, mul_ite, ite_mul, eq_comm]
  split_ifs <;> ring

/-- The diagonal polynomial is 1+(k-1)t². -/
theorem cliqueKernel_square_diagonal {A : Type*} [Fintype A] (t : ℝ) (i : A) :
    ((cliqueKernel t : Matrix A A ℝ) * (cliqueKernel t : Matrix A A ℝ)) i i = 1 + (Fintype.card A-1 : ℝ)*t^2 := by
  rw [cliqueKernel_square]
  simp only [ite_true]
  ring

/-- The off-diagonal polynomial is 2t+(k-2)t². -/
theorem cliqueKernel_square_offDiagonal {A : Type*} [Fintype A] (t : ℝ) (i j : A)
    (h : i ≠ j) :
    ((cliqueKernel t : Matrix A A ℝ) * (cliqueKernel t : Matrix A A ℝ)) i j = 2*t + (Fintype.card A-2 : ℝ)*t^2 := by
  rw [cliqueKernel_square, if_neg h]
  ring

end PlanarHom.HammingKernelTensor

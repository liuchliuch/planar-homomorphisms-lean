import PlanarHom.PottsCenteredExpansion
import Mathlib.LinearAlgebra.Matrix.Trace

/-! NEW reconstruction: exact centered path and cycle contractions. These
identities apply to the literal q*I-J entries used in the coefficient expansion. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered

theorem interaction_comp (q : ℕ) (i j : Fin q) :
    (∑ c : Fin q,interaction q i c*interaction q c j)=(q:ℚ)*interaction q i j := by
  have he (c : Fin q) : interaction q i c*interaction q c j=
      (if c=i then (q:ℚ)*(if i=j then (q:ℚ) else 0) else 0)-
        (if c=i then (q:ℚ) else 0)-(if c=j then (q:ℚ) else 0)+1 := by
    by_cases hi : c=i
    · subst c
      by_cases hj : i=j <;> simp [interaction,hj] <;> ring
    · by_cases hj : c=j
      · subst c
        simp [interaction,hi,Ne.symm hi]
        ring
      · simp [interaction,hi,Ne.symm hi,hj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp [interaction]
  split_ifs <;> ring

def interactionMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := Matrix.of (interaction q)

@[simp] theorem interactionMatrix_apply (q : ℕ) (i j : Fin q) : interactionMatrix q i j=interaction q i j := rfl

theorem interaction_matrix_mul (q : ℕ) :
    (interactionMatrix q)*(interactionMatrix q)=
      (q:ℚ) • (interactionMatrix q) := by
  ext i j
  simpa only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,interactionMatrix_apply] using interaction_comp q i j

/-- The actual transfer matrix for every positive-length path. -/
theorem interaction_matrix_pow (q n : ℕ) :
    (interactionMatrix q)^(n+1)=(q:ℚ)^n • interactionMatrix q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ _ (n+1),ih,smul_mul_assoc,interaction_matrix_mul,smul_smul]
    simp [pow_succ]

theorem interaction_trace (q : ℕ) :
    Matrix.trace (interactionMatrix q)=(q:ℚ)*((q:ℚ)-1) := by
  simp [Matrix.trace,Matrix.diag,interactionMatrix,interaction]
  ring

theorem interaction_cycle_trace (q n : ℕ) :
    Matrix.trace ((interactionMatrix q)^(n+1))=
      (q:ℚ)^(n+1)*((q:ℚ)-1) := by
  rw [interaction_matrix_pow,Matrix.trace_smul,interaction_trace]
  simp only [smul_eq_mul,pow_succ]
  ring
end PlanarHom.PottsCentered

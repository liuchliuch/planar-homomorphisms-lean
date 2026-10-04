import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The literal relative-trace identity in Remark3.4. Different sample fields
are handled individually; known base-field values descend before interpolation. -/
noncomputable section
namespace PlanarHom.TraceFieldDescent
variable {K L : Type} [Field K] [Field L] [CharZero K] [Algebra K L] [FiniteDimensional K L]

def normalizedTrace (z : L) : K := Algebra.trace K L z / (Module.finrank K L : K)

@[simp] theorem normalizedTrace_algebraMap (a : K) :
    normalizedTrace (L:=L) (algebraMap K L a) = a := by
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  rw [normalizedTrace, Algebra.trace_algebraMap, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hn

/-- The conversion is valid exactly on values proved to belong to the original
base field; no such membership is presumed for arbitrary extension values. -/
theorem normalizedTrace_eq_of_base_value (z : L) (a : K) (h : algebraMap K L a=z) :
    normalizedTrace z = a := by rw [←h,normalizedTrace_algebraMap]

/-- The source's bounded-dimensional multiplication-matrix realization of trace. -/
theorem normalizedTrace_matrix_formula {d : ℕ} (b : Module.Basis (Fin d) K L) (z : L) :
    normalizedTrace z = (Algebra.leftMulMatrix b z).trace / (d : K) := by
  rw [normalizedTrace, Algebra.trace_eq_matrix_trace b]
  congr 1
  rw [Module.finrank_eq_card_basis b,Fintype.card_fin]

end PlanarHom.TraceFieldDescent

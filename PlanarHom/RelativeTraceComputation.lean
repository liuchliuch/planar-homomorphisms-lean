import PlanarHom.FixedFieldEncodingTransport
import Mathlib.FieldTheory.NormalizedTrace

/-! Literal normalized relative trace in source Remark3.4. It is an actual
fixed-presentation polynomial-time map, and returns every known base-field
value exactly. Variable-field algorithms use their separately proved uniform
presentation/descent bounds; no compositum is formed by this statement. -/
noncomputable section
namespace PlanarHom.RelativeTraceComputation
open Complexity
variable {K L : Type} [Field K] [Field L] [CharZero K]
variable [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
variable [FiniteDimensional K L]

def descent : L→ₗ[ℚ] K := (Algebra.normalizedTrace K L).restrictScalars ℚ

theorem descent_eq_trace_div_degree (x : L) :
    descent (K:=K) (L:=L) x=Algebra.trace K L x/(Module.finrank K L : K) := by
  change Algebra.normalizedTrace K L x=_
  rw [Algebra.normalizedTrace_eq_of_fininteDimensional_apply]
  simp only [smul_eq_mul,div_eq_mul_inv]
  exact mul_comm _ _

theorem descent_algebraMap (x : K) :
    descent (K:=K) (L:=L) (algebraMap K L x)=x := by
  rw [descent_eq_trace_div_degree,Algebra.trace_algebraMap]
  have hn : (Module.finrank K L : K)≠0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R:=K) (M:=L)))
  simpa only [nsmul_eq_mul] using mul_div_cancel_left₀ x hn

theorem fp_descent {d e : ℕ} (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) :
    FP (numberFieldEncoding bL) (numberFieldEncoding bK) (descent (K:=K) (L:=L)) :=
  FixedFieldEncodingTransport.fp_linearMap bL bK descent

/-- A sample answer known to be in the base field is returned in its original
basis by the concrete normalized-trace machine. -/
theorem fp_base_value {α : Type} (ea : BitEncoding α) {d e : ℕ}
    (bK : Module.Basis (Fin d) ℚ K) (bL : Module.Basis (Fin e) ℚ L)
    (f : α→K) (hf : FP ea (numberFieldEncoding bL) (fun x=>algebraMap K L (f x))) :
    FP ea (numberFieldEncoding bK) f :=
  (hf.comp (fp_descent bK bL)).congr (fun x=>descent_algebraMap (f x))

end PlanarHom.RelativeTraceComputation

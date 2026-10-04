import PlanarHom.CountingCookLevinNorMachines
import PlanarHom.BinarySubtractionMachine

/-! Fixed arithmetic formulas for uniform circuit register addresses, evaluated
by actual binary natural arithmetic machines. -/
namespace PlanarHom.CountingCookLevin
open Complexity

inductive IndexExpr (V : Type) where
  | var (v : V)
  | constant (n : ℕ)
  | add (a b : IndexExpr V)
  | mul (a b : IndexExpr V)
  | sub (a b : IndexExpr V)

namespace IndexExpr

def eval {V : Type} (ρ : V → ℕ) : IndexExpr V → ℕ
  | .var v => ρ v
  | .constant n => n
  | .add a b => a.eval ρ+b.eval ρ
  | .mul a b => a.eval ρ*b.eval ρ
  | .sub a b => a.eval ρ-b.eval ρ

theorem fp_eval {d : ℕ} (e : IndexExpr (Fin d)) :
    FP (BitEncoding.nat.vector d) BitEncoding.nat (fun ρ => e.eval ρ) := by
  induction e with
  | var v => exact FixedVectorMachines.fp_coordinate BitEncoding.nat d v
  | constant n => exact fp_const _ _ n
  | add a b ha hb => exact (ha.pair hb).comp BinaryArithmetic.fp_addition
  | mul a b ha hb => exact (ha.pair hb).comp BinaryArithmetic.fp_multiplication
  | sub a b ha hb => exact (ha.pair hb).comp BinaryArithmetic.fp_subtraction

/-- The same compiler applies when each input coordinate is already computed
by an actual encoded polynomial-time program. -/
theorem fp_eval_comp {A : Type} (ea : BitEncoding A) {d : ℕ} (e : IndexExpr (Fin d))
    (v : A → Fin d → ℕ) (hv : ∀ i,FP ea BitEncoding.nat (fun a => v a i)) :
    FP ea BitEncoding.nat (fun a => e.eval (v a)) :=
  (FixedVectorMachines.fp_assemble ea BitEncoding.nat d v hv).comp e.fp_eval

end IndexExpr
end PlanarHom.CountingCookLevin

import PlanarHom.MaterializedPowerMachines
import PlanarHom.FixedExponentProductMachines

/-! Products over fixed-dimensional, fully materialized field and exponent vectors. -/
namespace PlanarHom.MaterializedExponentProductMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {dimension t : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Input (K : Type) (t : ℕ) := ℕ × ((Fin t → K) × (Fin t → ℕ))

/-- Unary cap followed by the literal field vector and binary exponent vector. -/
noncomputable def inputEncoding (t : ℕ) : BitEncoding (Input K t) :=
  BitEncoding.unaryNat.prod (((numberFieldEncoding basis).vector t).prod (BitEncoding.nat.vector t))

def product (p : Input K t) : K := ∏ i, p.2.1 i ^ min p.1 (p.2.2 i)

/-- Fixed-dimensional circuit of actual varying-base power machines. -/
theorem fp_product : FP (inputEncoding basis t) (numberFieldEncoding basis) (product : Input K t → K) := by
  have hc := fp_fst BitEncoding.unaryNat (((numberFieldEncoding basis).vector t).prod (BitEncoding.nat.vector t))
  have hv := fp_snd BitEncoding.unaryNat (((numberFieldEncoding basis).vector t).prod (BitEncoding.nat.vector t))
  have ha := hv.comp (fp_fst ((numberFieldEncoding basis).vector t) (BitEncoding.nat.vector t))
  have hr := hv.comp (fp_snd ((numberFieldEncoding basis).vector t) (BitEncoding.nat.vector t))
  apply FixedExponentProductMachines.fp_finset_product basis (inputEncoding basis t) Finset.univ
  intro i _
  have hai := ha.comp (FixedVectorMachines.fp_coordinate (numberFieldEncoding basis) t i)
  have hri := hr.comp (FixedVectorMachines.fp_coordinate BitEncoding.nat t i)
  exact (hc.pair (hai.pair hri)).comp (MaterializedPowerMachines.fp_boundedPower basis)

omit [Algebra ℚ K] in
/-- The cap disappears whenever the enumerator supplied an honest exponent vector. -/
theorem product_eq (m : ℕ) (A : Fin t → K) (r : Fin t → ℕ) (hr : ∀ i, r i ≤ m) :
    product (m, (A, r)) = ∏ i, A i ^ r i :=
  FixedExponentProductMachines.clipped_product_eq A m r hr

end PlanarHom.MaterializedExponentProductMachines

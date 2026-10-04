import PlanarHom.FixedPowerMachines
import PlanarHom.FixedVectorMachines

/-! Actual evaluation of fixed-alphabet exponent vectors, with an explicit
unary cap and a fixed number of field multiplication circuits. -/
namespace PlanarHom.FixedExponentProductMachines
open Turing PlanarHom.Complexity
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {dimension t : ℕ}

/-- A fixed finite product of already compiled expressions is a finite circuit,
not a dynamic iteration or unbounded host-language product. -/
theorem fp_finset_product {α ι : Type} [DecidableEq ι]
    (basis : Module.Basis (Fin dimension) ℚ K) (ea : BitEncoding α)
    (s : Finset ι) (f : ι→α→K)
    (hf : ∀i∈s,FP ea (numberFieldEncoding basis) (f i)) :
    FP ea (numberFieldEncoding basis) (fun a=>∏i∈s,f i a):=by
  induction s using Finset.induction_on with
  | empty=>simpa using fp_const ea (numberFieldEncoding basis) (1 : K)
  | @insert i s hi ih=>
    have ha:=hf i (by simp)
    have hs:=ih (fun j hj=>hf j (by simp [hj]))
    exact ((ha.pair hs).comp (PlanarHom.FixedFieldArithmetic.fp_multiplication basis)).congr
      (fun a=>by simp [hi])

/-- The varying exponent vector has fixed dimension; the varying cap is unary. -/
def inputEncoding (t : ℕ) : BitEncoding (ℕ × (Fin t→ℕ)):=
  BitEncoding.unaryNat.prod (BitEncoding.nat.vector t)

theorem fp_product (basis : Module.Basis (Fin dimension) ℚ K) (A : Fin t→K) :
    FP (inputEncoding t) (numberFieldEncoding basis)
      (fun p=>∏i,A i^(min p.1 (p.2 i))):=by
  have hc:=PairProjectionMachines.fp_fst BitEncoding.unaryNat (BitEncoding.nat.vector t)
  have he:=PairProjectionMachines.fp_snd BitEncoding.unaryNat (BitEncoding.nat.vector t)
  apply fp_finset_product basis (inputEncoding t) Finset.univ
  intro i _
  have hi:=he.comp (PlanarHom.FixedVectorMachines.fp_coordinate BitEncoding.nat t i)
  exact (hc.pair hi).comp ⟨PlanarHom.FixedPowerMachines.boundedComputer basis (A i)⟩

omit [Algebra ℚ K] in
theorem clipped_product_eq (A : Fin t→K) (m : ℕ) (r : Fin t→ℕ) (hr : ∀i,r i≤m) :
    (∏i,A i^(min m (r i)))=∏i,A i^(r i):=by
  apply Finset.prod_congr rfl
  intro i _
  rw [min_eq_right (hr i)]

/-- Source and target products are computed from the same representative
vector. No ability to evaluate an abstract collision map is assumed. -/
theorem fp_product_pair (basis : Module.Basis (Fin dimension) ℚ K) (A B : Fin t→K) :
    FP (inputEncoding t) ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
      (fun p=>(∏i,A i^(min p.1 (p.2 i)),∏i,B i^(min p.1 (p.2 i)))):=
  (fp_product basis A).pair (fp_product basis B)

end PlanarHom.FixedExponentProductMachines

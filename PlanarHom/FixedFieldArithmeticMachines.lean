import PlanarHom.FixedFieldArithmeticBits
import PlanarHom.FixedVectorMachines
import PlanarHom.FiniteRationalCircuits

/-! # Genuine polynomial-time exact arithmetic in a fixed rational number-field basis -/
namespace PlanarHom.FixedFieldArithmetic
open Complexity ArithmeticCircuitPrimitives RationalCircuits BinaryArithmetic
open IntegerCoordinateBounds FieldCoordinateCertificates PairProjectionMachines
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Coordinates are extracted by an actual fixed number of framed-pair parsers. -/
theorem fp_coordinate (i : Fin dimension) :
    FP (numberFieldEncoding basis) BitEncoding.rat (fun x => basis.equivFun x i) := by
  exact FP.transportInput basis.equivFun (fun _ => rfl)
    (FixedVectorMachines.fp_coordinate BitEncoding.rat dimension i)

/-- Assemble exact canonical coordinates and reinterpret the identical output word. -/
theorem fp_of_coordinates {α : Type} (ea : BitEncoding α) (f : α→K)
    (hf : ∀ i, FP ea BitEncoding.rat (fun a => basis.equivFun (f a) i)) :
    FP ea (numberFieldEncoding basis) f := by
  exact (FixedVectorMachines.fp_assemble ea BitEncoding.rat dimension
    (fun a => basis.equivFun (f a)) hf).transportOutput (fun _ => rfl)

theorem fp_addition : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p : K×K => p.1+p.2) := by
  apply fp_of_coordinates
  intro i
  have hl := (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_coordinate basis i)
  have hr := (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_coordinate basis i)
  exact ((hl.pair hr).comp fp_rational_addition).congr (fun p => by simp)

theorem fp_negation : FP (numberFieldEncoding basis) (numberFieldEncoding basis) (fun x : K => -x) := by
  apply fp_of_coordinates
  intro i
  exact ((fp_coordinate basis i).comp fp_rational_negation).congr (fun x => by simp)

theorem fp_subtraction : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p : K×K => p.1-p.2) := by
  exact (((fp_id (numberFieldEncoding basis)).prodMap (fp_negation basis)).comp (fp_addition basis)).congr
    (fun p => by simp [Prod.map,sub_eq_add_neg])

/-- Each multiplication-matrix entry is a fixed linear rational circuit. -/
theorem fp_multiplication_matrix (i j : Fin dimension) :
    FP (numberFieldEncoding basis) BitEncoding.rat (fun x => multiplicationMatrix basis x i j) := by
  have ht (k : Fin dimension) := ((fp_coordinate basis k).pair
    (fp_const (numberFieldEncoding basis) BitEncoding.rat (multiplicationMatrix basis (basis k) i j))).comp
      fp_rational_multiplication
  exact (FiniteRationalCircuits.fp_sum (numberFieldEncoding basis) Finset.univ
    (fun x k => basis.equivFun x k * multiplicationMatrix basis (basis k) i j) ht).congr
      (fun x => (multiplicationMatrix_expansion basis x i j).symm)

theorem fp_multiplication : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p : K×K => p.1*p.2) := by
  apply fp_of_coordinates
  intro i
  have ht (j : Fin dimension) :=
    (((fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_multiplication_matrix basis i j)).pair
      ((fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_coordinate basis j))).comp
        fp_rational_multiplication
  exact (FiniteRationalCircuits.fp_sum ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) Finset.univ
    (fun p j => multiplicationMatrix basis p.2 i j * basis.equivFun p.1 j) ht).congr
    (fun p => by simpa only [Matrix.mulVec,dotProduct] using congrFun (multiplicationMatrix_mulVec basis p.2 p.1) i)

/-- Total inverse uses a fixed determinant/Cramer circuit, with no search or oracle. -/
theorem fp_inverse : FP (numberFieldEncoding basis) (numberFieldEncoding basis) (fun x : K => x⁻¹) := by
  apply fp_of_coordinates
  intro i
  have hd := FiniteRationalCircuits.fp_det (numberFieldEncoding basis)
    (multiplicationMatrix basis) (fp_multiplication_matrix basis)
  have hn := FiniteRationalCircuits.fp_cramer (numberFieldEncoding basis)
    (multiplicationMatrix basis) (fun _ => basis.equivFun 1) (fp_multiplication_matrix basis)
    (fun j => fp_const (numberFieldEncoding basis) BitEncoding.rat (basis.equivFun 1 j)) i
  exact ((hn.pair hd).comp fp_rational_division).congr (fun x => (inverse_coordinate basis x i).symm)

theorem fp_division : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p : K×K => p.1/p.2) := by
  exact (((fp_id (numberFieldEncoding basis)).prodMap (fp_inverse basis)).comp (fp_multiplication basis)).congr
    (fun p => by simp [Prod.map,div_eq_mul_inv])

/-- Exact equality is a fixed finite conjunction of canonical rational comparisons. -/
theorem fp_equality [DecidableEq K] : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    BitEncoding.bool (fun p : K×K => decide (p.1=p.2)) := by
  classical
  have ht (i : Fin dimension) :=
    (((fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_coordinate basis i)).pair
      ((fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)).comp (fp_coordinate basis i))).comp
        fp_rational_equality
  exact (FiniteRationalCircuits.fp_all ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) Finset.univ
    (fun p i => decide (basis.equivFun p.1 i=basis.equivFun p.2 i)) ht).congr
    (fun p => by
      simp only [Finset.mem_univ,forall_const,decide_eq_true_eq,decide_eq_decide]
      exact ⟨fun h => basis.equivFun.injective (funext h),fun h => by rw [h]; intro i; rfl⟩)

end PlanarHom.FixedFieldArithmetic

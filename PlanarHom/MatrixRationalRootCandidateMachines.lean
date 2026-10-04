import PlanarHom.MatrixRationalRootCandidates
import PlanarHom.PolynomialIntegerRootCandidateMachines
import PlanarHom.FixedCharacteristicPolynomialMachines

/-! # Actual rational characteristic-root candidate machines

Every input-dependent denominator, integer entry, root bound and shifted
characteristic coefficient is materialized by exact binary arithmetic.
-/

noncomputable section
namespace PlanarHom.MatrixRationalRootCandidateMachines
open Complexity BinaryArithmetic RationalCircuits ArithmeticCircuitPrimitives
open PairProjectionMachines MatrixRationalRootBounds MatrixRationalRootCandidates
open scoped BigOperators

theorem fp_natSum {α J : Type} (ea : BitEncoding α) (s : Finset J) (f : α → J → ℕ)
    (hf : ∀ j, FP ea BitEncoding.nat (fun a => f a j)) :
    FP ea BitEncoding.nat (fun a => ∑ j ∈ s, f a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.nat 0
  | @insert j s hj ih =>
    exact (((hf j).pair ih).comp fp_addition).congr (fun a => by simp [Finset.sum_insert, hj])

theorem fp_natProd {α J : Type} (ea : BitEncoding α) (s : Finset J) (f : α → J → ℕ)
    (hf : ∀ j, FP ea BitEncoding.nat (fun a => f a j)) :
    FP ea BitEncoding.nat (fun a => ∏ j ∈ s, f a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.nat 1
  | @insert j s hj ih =>
    exact (((hf j).pair ih).comp fp_multiplication).congr
      (fun a => by simp [Finset.prod_insert, hj])

variable {α I : Type} [Fintype I] [DecidableEq I]
variable (ea : BitEncoding α) (A : α → Matrix I I ℚ)
variable (hA : ∀ i j, FP ea BitEncoding.rat (fun a => A a i j))
include hA

theorem fp_denominator : FP ea BitEncoding.nat (fun a => denominator (A a)) :=
  fp_natProd ea Finset.univ _ (fun ij => (hA ij.1 ij.2).comp fp_rat_den)

theorem fp_integerMatrix (i j : I) : FP ea BitEncoding.int
    (fun a => integerMatrix (A a) i j) := by
  have hd := ((fp_denominator ea A hA).pair ((hA i j).comp fp_rat_den)).comp fp_division
  have hq := (hd.comp (fp_fst BitEncoding.nat BitEncoding.nat)).comp fp_nat_int
  exact (((hA i j).comp fp_rat_num).pair hq).comp fp_int_mul

theorem fp_bound : FP ea BitEncoding.nat (fun a => bound (A a)) :=
  (fp_natSum ea Finset.univ (fun a (ij : I×I) => (integerMatrix (A a) ij.1 ij.2).natAbs) (fun ij =>
    (fp_integerMatrix ea A hA ij.1 ij.2).comp fp_int_natAbs)).comp fp_successor

theorem fp_shifted (i j : I) : FP ea BitEncoding.rat (fun a => shifted (A a) i j) := by
  have hz := (fp_integerMatrix ea A hA i j).comp fp_int_rat
  have hb := (fp_bound ea A hA).comp BoundedPolynomialEvaluationMachines.fp_natCast
  have ht := (hb.pair (fp_const ea BitEncoding.rat ((1 : Matrix I I ℚ) i j))).comp
    fp_rational_multiplication
  exact (hz.pair ht).comp fp_rational_addition

theorem fp_shiftedCoefficients (k : ℕ) :
    FP ea BitEncoding.rat (fun a => (shifted (A a)).charpoly.coeff k) :=
  FixedCharacteristicPolynomialMachines.fp_charpoly_coeff ea (fun a => shifted (A a))
    (fp_shifted ea A hA) k

theorem fp_integerCandidates : FP ea BitEncoding.nat.list
    (fun a => PolynomialIntegerRootCandidates.candidates (Fintype.card I)
      (shifted (A a)).charpoly 0 (2*bound (A a)+1)) := by
  have hp := PolynomialIntegerRootCandidateMachines.fp_candidates ea
    (fun a => (shifted (A a)).charpoly) (Fintype.card I)
    (fun a => by simp) (fp_shiftedCoefficients ea A hA)
  have hb := ((((fp_const ea BitEncoding.nat 2).pair (fp_bound ea A hA)).comp
    fp_multiplication).comp fp_successor)
  exact ((fp_id ea).pair ((fp_const ea BitEncoding.nat 0).pair hb)).comp hp

theorem fp_decodeCandidate : FP (ea.prod BitEncoding.nat) BitEncoding.rat
    (fun a => ((a.2:ℚ)-(bound (A a.1):ℚ))/(denominator (A a.1):ℚ)) := by
  have hx := fp_fst ea BitEncoding.nat
  have hi := (fp_snd ea BitEncoding.nat).comp BoundedPolynomialEvaluationMachines.fp_natCast
  have hb := (hx.comp (fp_bound ea A hA)).comp BoundedPolynomialEvaluationMachines.fp_natCast
  have hd := (hx.comp (fp_denominator ea A hA)).comp BoundedPolynomialEvaluationMachines.fp_natCast
  exact (((hi.pair hb).comp fp_rational_subtraction).pair hd).comp fp_rational_division

/-- Full FP candidate enumeration for every rational characteristic root of
the input matrix. Candidate count depends only on the fixed matrix dimension. -/
theorem fp_candidates : FP ea BitEncoding.rat.list (fun a => candidates (A a)) := by
  have hm := ListContextMachines.fp_mapWithContext ea BitEncoding.nat BitEncoding.rat
    (fun a => ((a.2:ℚ)-(bound (A a.1):ℚ))/(denominator (A a.1):ℚ))
    (fp_decodeCandidate ea A hA)
  exact ((fp_id ea).pair (fp_integerCandidates ea A hA)).comp hm

end PlanarHom.MatrixRationalRootCandidateMachines

import PlanarHom.RestrictedIterationMachine
import PlanarHom.ArithmeticCircuitPrimitives

/-! Actual unary arithmetic and fixed polynomial bounds, with explicit output cost. -/
namespace PlanarHom.UnaryPolynomialMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines

theorem encode_add (a b : ℕ) : BitEncoding.unaryNat.encode (a + b) =
    BitEncoding.unaryNat.encode a ++ BitEncoding.unaryNat.encode b := by
  induction a with
  | zero => simp [BitEncoding.unaryNat, Computability.unaryEncodeNat]
  | succ a ih => simpa only [Nat.succ_add, BitEncoding.unaryNat, Computability.unaryEncodeNat,
      List.cons_append] using congrArg (List.cons true) ih

theorem fp_add : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat) BitEncoding.unaryNat
    (fun p : ℕ × ℕ => p.1 + p.2) := by
  have hw : FP BitEncoding.unaryNat BitEncoding.bits BitEncoding.unaryNat.encode :=
    fp_code_view _ _ _ (fun _ => rfl)
  have ha := (fp_fst BitEncoding.unaryNat BitEncoding.unaryNat).comp hw
  have hb := (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat).comp hw
  exact ((ha.pair hb).comp PairProjectionMachines.fp_append).transportOutput
    (fun p => (encode_add p.1 p.2).symm)

def addStep (s : ℕ × ℕ) : ℕ × ℕ := (s.1, s.2 + s.1)

theorem addStep_iterate (a z n : ℕ) : addStep^[n] (a,z) = (a,z+n*a) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, addStep, Nat.succ_mul, Nat.add_assoc]

theorem fp_addStep : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
    (BitEncoding.unaryNat.prod BitEncoding.unaryNat) addStep := by
  have ha := fp_fst BitEncoding.unaryNat BitEncoding.unaryNat
  have hz := fp_snd BitEncoding.unaryNat BitEncoding.unaryNat
  exact ha.pair ((hz.pair ha).comp fp_add)

theorem fp_mul : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat) BitEncoding.unaryNat
    (fun p : ℕ × ℕ => p.1 * p.2) := by
  let e := BitEncoding.unaryNat.prod BitEncoding.unaryNat
  obtain ⟨body⟩ := fp_addStep
  let p : Polynomial ℕ := Polynomial.C 4 * (Polynomial.X + 1) ^ 2
  have hs (n : ℕ) (s : ℕ × ℕ) (i : ℕ) (hi : i ≤ n) :
      (e.encode (addStep^[i] s)).length ≤ p.eval ((BitEncoding.unaryNat.prod e).encode (n,s)).length := by
    rw [show s = (s.1,s.2) from rfl, addStep_iterate]
    simp only [e, BitEncoding.prod_length, BitEncoding.unaryNat_length, p, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hm := Nat.mul_le_mul_right s.1 hi
    nlinarith [sq_nonneg (n : ℤ), sq_nonneg (s.1 : ℤ), sq_nonneg (s.2 : ℤ)]
  have hi : FP (BitEncoding.unaryNat.prod e) e (fun p => addStep^[p.1] p.2) :=
    ⟨BoundedIterationMachine.computer e addStep body p hs⟩
  have hn := fp_fst BitEncoding.unaryNat BitEncoding.unaryNat
  have ha := fp_snd BitEncoding.unaryNat BitEncoding.unaryNat
  have hz := fp_const (BitEncoding.unaryNat.prod BitEncoding.unaryNat) BitEncoding.unaryNat 0
  exact ((((hn.pair (ha.pair hz)).comp hi).comp
    (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat))).congr (fun _ => by simp [addStep_iterate])

/-- The polynomial is fixed program data; its possibly large value is physically
emitted in unary by the above addition and multiplication machines. -/
theorem fp_eval (p : Polynomial ℕ) : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n => p.eval n) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using fp_const BitEncoding.unaryNat BitEncoding.unaryNat a
  | add p q hp hq => exact ((hp.pair hq).comp fp_add).congr (fun n => by simp)
  | monomial n a ih =>
    exact ((ih.pair (fp_id BitEncoding.unaryNat)).comp fp_mul).congr (fun x => by
      simp [pow_succ, Nat.mul_assoc])

/-- Fixed lower sample offsets are compiled as unary addition too. -/
theorem fp_offset (n₀ : ℕ) : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n => n₀ + n) :=
  ((fp_const BitEncoding.unaryNat BitEncoding.unaryNat n₀).pair (fp_id BitEncoding.unaryNat)).comp fp_add

end PlanarHom.UnaryPolynomialMachines

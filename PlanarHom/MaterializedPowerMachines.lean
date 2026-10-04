import PlanarHom.MaterializedFieldHeights
import PlanarHom.RestrictedIterationMachine
import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.BoundedUnaryMachines

/-! Actual bounded iteration for powers of arbitrary materialized field elements. -/
namespace PlanarHom.MaterializedPowerMachines
open Turing Complexity ArithmeticCircuitPrimitives PairProjectionMachines MachineComposition
variable {K : Type} [Field K]

/-- Retain the actual base while multiplying the actual accumulator. -/
def powerStep (p : K × K) : K × K := (p.1, p.2 * p.1)

theorem powerStep_iterate (a z : K) (n : ℕ) :
    powerStep^[n] (a, z) = (a, z * a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, powerStep, pow_succ, mul_assoc]

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- The full base and accumulator remain in the loop state. -/
noncomputable def stateEncoding : BitEncoding (K × K) :=
  (numberFieldEncoding basis).prod (numberFieldEncoding basis)

theorem fp_powerStep : FP (stateEncoding basis) (stateEncoding basis) powerStep := by
  have ha := fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)
  have hz := fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)
  exact ha.pair ((hz.pair ha).comp (FixedFieldArithmetic.fp_multiplication basis))

/-- Every iterate has polynomial canonical size in the unary count and literal
base/accumulator words. Repeated factors are used only in this height proof. -/
theorem exists_iteration_encoding_bound : ∃ p : Polynomial ℕ, ∀ (n : ℕ) (s : K × K) (i : ℕ),
    i ≤ n → ((stateEncoding basis).encode (powerStep^[i] s)).length ≤
      p.eval ((BitEncoding.unaryNat.prod (stateEncoding basis)).encode (n, s)).length := by
  obtain ⟨data⟩ := IntegerCoordinateBounds.exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  let q := (EncodingSizeBounds.coordinateOutputPolynomial dimension
    (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).comp
      ((Polynomial.X + Polynomial.C 2) ^ 2)
  let p := Polynomial.C 2 * Polynomial.X + q + Polynomial.C 1
  refine ⟨p, fun n s i hi => ?_⟩
  let e := numberFieldEncoding basis
  let N := ((BitEncoding.unaryNat.prod (stateEncoding basis)).encode (n, s)).length
  have hN : N = 2 * n + (2 * (e.encode s.1).length + (e.encode s.2).length + 1) + 1 := by
    simp only [N, stateEncoding, BitEncoding.prod_length, BitEncoding.unaryNat_length]
    rfl
  have hn : n ≤ N := by omega
  have ha : (e.encode s.1).length ≤ N := by omega
  have hz : (e.encode s.2).length ≤ N := by omega
  have hlen : (s.2 :: List.replicate i s.1).length ≤ N + 1 := by simp; omega
  have hcode : ∀ x ∈ s.2 :: List.replicate i s.1, (e.encode x).length ≤ N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hz
    · have hx' := (List.mem_replicate.mp hx).2
      simpa [hx'] using ha
  have hb := (MaterializedFieldHeights.list_values_encoding_bound data _ N hlen hcode).1
  have hc : (e.encode (s.2 * s.1 ^ i)).length ≤ q.eval N := by
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, List.prod_cons, List.prod_replicate] using hb
  rw [show s = (s.1, s.2) from rfl, powerStep_iterate]
  change ((stateEncoding basis).encode (s.1, s.2 * s.1 ^ i)).length ≤ p.eval N
  conv_lhs => simp only [stateEncoding, BitEncoding.prod_length]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change 2 * (e.encode s.1).length + (e.encode (s.2 * s.1 ^ i)).length + 1 ≤ 2 * N + q.eval N + 1
  omega

/-- Actual ordinary iteration on all materialized starts, with no alphabet promise. -/
noncomputable def iterationComputer : TM2ComputableInPolyTime
    (BitEncoding.unaryNat.prod (stateEncoding basis)).toFinEncoding
    (stateEncoding basis).toFinEncoding (fun p => powerStep^[p.1] p.2) := by
  let p := Classical.choose (exists_iteration_encoding_bound basis)
  have hp := Classical.choose_spec (exists_iteration_encoding_bound basis)
  exact BoundedIterationMachine.computer (stateEncoding basis) powerStep
    (Classical.choice (fp_powerStep basis)) p hp

/-- Unary exponentiation with a varying, canonically encoded base. -/
theorem fp_power : FP (BitEncoding.unaryNat.prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p : ℕ × K => p.2 ^ p.1) := by
  let input := BitEncoding.unaryNat.prod (numberFieldEncoding basis)
  have hn := fp_fst BitEncoding.unaryNat (numberFieldEncoding basis)
  have ha := fp_snd BitEncoding.unaryNat (numberFieldEncoding basis)
  have hs := ha.pair (fp_const input (numberFieldEncoding basis) (1 : K))
  have hloop := ((hn.pair hs).comp ⟨iterationComputer basis⟩).comp
    (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))
  exact hloop.congr (fun p => by simp [powerStep_iterate])

/-- Binary exponent expansion is charged to an explicit unary cap. -/
theorem fp_boundedPower : FP
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).prod BitEncoding.nat))
    (numberFieldEncoding basis) (fun p : ℕ × (K × ℕ) => p.2.1 ^ min p.1 p.2.2) := by
  have hc := fp_fst BitEncoding.unaryNat ((numberFieldEncoding basis).prod BitEncoding.nat)
  have ht := fp_snd BitEncoding.unaryNat ((numberFieldEncoding basis).prod BitEncoding.nat)
  have ha := ht.comp (fp_fst (numberFieldEncoding basis) BitEncoding.nat)
  have hr := ht.comp (fp_snd (numberFieldEncoding basis) BitEncoding.nat)
  have hn := (hc.pair hr).comp ⟨BoundedUnaryMachines.computer⟩
  exact (hn.pair ha).comp (fp_power basis)

end PlanarHom.MaterializedPowerMachines

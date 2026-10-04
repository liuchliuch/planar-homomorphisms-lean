import PlanarHom.BooleanEffectiveSampling

/-! Source-length specialization: the input is only the unary product length.
All class multiplicities and the requested interpolation degree are fixed data. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanEffectiveLengthSamples
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines BooleanEffectiveSampling
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension b : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- The total factor cap, outer-interpolation count, and exact class totals
are computed from the literal unary source product length. -/
def prepare (d : Fin b → ℕ) (ell m : ℕ) : BooleanEffectiveSampling.Input :=
  ((∑ i,d i)*m,(ell*m+1,List.ofFn (fun i => d i*m)))

theorem fp_prepare (d : Fin b → ℕ) (ell : ℕ) :
    FP BitEncoding.unaryNat BooleanEffectiveSampling.inputEncoding (prepare d ell) := by
  have hcap : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun m => (∑ i,d i)*m) :=
    (UnaryPolynomialMachines.fp_eval (Polynomial.C (∑ i,d i)*Polynomial.X)).congr
      (fun m => by simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X])
  have hL : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun m => ell*m+1) :=
    (UnaryPolynomialMachines.fp_eval (Polynomial.C ell*Polynomial.X+1)).congr
      (fun m => by simp)
  have hv := FixedVectorMachines.fp_assemble BitEncoding.unaryNat BitEncoding.nat b
    (fun m i => d i*m) (fun i =>
      ((UnaryPolynomialMachines.fp_eval (Polynomial.C (d i)*Polynomial.X)).comp
        UnaryNatConversionMachine.fp_conversion).congr (fun m => by simp))
  have hlist : FP (BitEncoding.nat.vector b) BitEncoding.nat.list
      (List.ofFn : (Fin b → ℕ) → List ℕ) :=
    fp_code_view _ _ _ (fun _ => rfl)
  exact hcap.pair (hL.pair (hv.comp hlist))

def samples (c a w : Fin b → K) (d : Fin b → ℕ) (ell m : ℕ) : List ℚ :=
  BooleanEffectiveSampling.candidates c a w (prepare d ell m)

include basis in
/-- Actual polynomial bit cost as a function of the original unary length,
including every count, grid, pair test, and exact field operation. -/
theorem fp_samples (c a w : Fin b → K) (d : Fin b → ℕ) (ell : ℕ) :
    FP BitEncoding.unaryNat BitEncoding.rat.list (samples c a w d ell) :=
  (fp_prepare d ell).comp (BooleanEffectiveSampling.fp_candidates basis c a w)

@[simp] theorem totals_prepare (d : Fin b → ℕ) (ell m : ℕ) :
    BooleanEffectiveSampling.totals b (prepare d ell m)=fun i => d i*m := by
  funext i
  simp only [BooleanEffectiveSampling.totals,prepare]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]
  exact min_eq_right (Nat.mul_le_mul_right m
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))

theorem samples_length_ge (f : K →+* ℝ) (c a w : Fin b → K) (d : Fin b → ℕ) (ell m : ℕ)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i))) :
    ell*m+1≤(samples c a w d ell m).length :=
  BooleanEffectiveSampling.length_candidates_ge f c a w (prepare d ell m) hp

theorem samples_nodup (c a w : Fin b → K) (d : Fin b → ℕ) (ell m : ℕ) :
    (samples c a w d ell m).Nodup :=
  BooleanEffectiveSampling.nodup_candidates c a w (prepare d ell m)

/-- The emitted rational samples separate every bounded product family at
this length, enough for the source's unequal-class replacement target. -/
theorem samples_separate {I : Type*} (f : K →+* ℝ) (c a w : Fin b → K)
    (d : Fin b → ℕ) (ell m : ℕ) (q : ℚ) (hq : q∈samples c a w d ell m)
    (k : I → Fin b → ℕ) (hk : ∀ i g, k i g≤d g*m) :
    BooleanExceptionalSampling.SeparatesUnequalCounts
      (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i)) (fun i => d i*m) k (q : ℝ) := by
  have ht := totals_prepare d ell m
  have h := BooleanEffectiveSampling.candidate_separates f c a w (prepare d ell m) q hq k
    (by simpa only [ht] using hk)
  simpa only [ht] using h

theorem samples_bounds (c a w : Fin b → K) (d : Fin b → ℕ) (ell m : ℕ) (q : ℚ)
    (hq : q∈samples c a w d ell m) :
    (q : ℝ)∈Set.Ioo (0 : ℝ) 1 ∧ 0<q.num ∧
      q.num.natAbs≤(BooleanEffectiveSampling.capPolynomial b).eval ((∑ i,d i)*m)+ell*m+1 ∧
      0<q.den ∧ q.den≤(BooleanEffectiveSampling.capPolynomial b).eval ((∑ i,d i)*m)+ell*m+2 := by
  simpa [prepare,Nat.add_assoc] using
    BooleanEffectiveSampling.candidate_bounds c a w (prepare d ell m) q hq

end PlanarHom.BooleanEffectiveLengthSamples

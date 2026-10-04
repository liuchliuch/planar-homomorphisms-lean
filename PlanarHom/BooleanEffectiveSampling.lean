import PlanarHom.BooleanNormSampleCompleteness
import PlanarHom.BooleanFieldNormSamples

/-! Automatic polynomial-size grid generation followed by the actual fixed-field
norm selector. The caller supplies only unary cap/desired count and an ordinary
binary count list; the candidate grid bound is itself computed by a real machine. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanEffectiveSampling
open Complexity PairProjectionMachines
open BooleanExceptionalSampling
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension b : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- Unary cap, desired number of samples, and binary total counts. -/
abbrev Input := ℕ × (ℕ × List ℕ)
def inputEncoding : BitEncoding Input :=
  BitEncoding.unaryNat.prod (BitEncoding.unaryNat.prod BitEncoding.nat.list)

/-- A fixed polynomial upper bound on the total exceptional norm roots. -/
def capPolynomial (b : ℕ) : Polynomial ℕ :=
  ((Polynomial.C b*Polynomial.X+1)^b)^2 *
    (Polynomial.C (2^b)*(Polynomial.C b*Polynomial.X))

@[simp] theorem capPolynomial_eval (b M : ℕ) :
    (capPolynomial b).eval M=(((b*M+1)^b)^2)*(2^b*(b*M)) := by
  simp [capPolynomial]

/-- This prepares the literal unary grid count, rather than assuming it is
cheap to materialize from a binary integer. -/
def prepare (b : ℕ) (p : Input) : BooleanNormSampleSearch.Input :=
  ((capPolynomial b).eval p.1+p.2.1,(p.1,p.2.2))

theorem fp_prepare (b : ℕ) : FP inputEncoding BooleanNormSampleSearch.inputEncoding (prepare b) := by
  have hM := fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have ht := fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hL := ht.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat.list)
  have hns := ht.comp (fp_snd BitEncoding.unaryNat BitEncoding.nat.list)
  have hN := ((hM.comp (UnaryPolynomialMachines.fp_eval (capPolynomial b))).pair hL).comp
    UnaryPolynomialMachines.fp_add
  exact hN.pair (hM.pair hns)

def candidates (c a w : Fin b → K) (p : Input) : List ℚ :=
  BooleanNormSampleMachines.candidates c a w (prepare b p)
def search (c a w : Fin b → K) (p : Input) : ℚ :=
  BooleanNormSampleMachines.search c a w (prepare b p)

include basis in
/-- End-to-end FP, polynomial in the honestly encoded cap and desired count.
There is no assumed tester, enumerator, or arithmetic machine in this theorem. -/
theorem fp_candidates (c a w : Fin b → K) :
    FP inputEncoding BitEncoding.rat.list (candidates c a w) :=
  (fp_prepare b).comp (BooleanNormSampleMachines.fp_candidates basis c a w)

include basis in
theorem fp_search (c a w : Fin b → K) : FP inputEncoding BitEncoding.rat (search c a w) :=
  (fp_prepare b).comp (BooleanNormSampleMachines.fp_search basis c a w)

/-- The semantics of the clipped totals are explicit on every raw input. -/
def totals (b : ℕ) (p : Input) (i : Fin b) : ℕ := min p.1 (p.2.2.getD i.val 0)

@[simp] theorem counts_prepare (b : ℕ) (p : Input) :
    BooleanNormSampleMachines.counts (b := b) (prepare b p)=totals b p := rfl

theorem total_sum_le (b : ℕ) (p : Input) : (∑ i, totals b p i)≤b*p.1 := by
  calc
    (∑ i, totals b p i)≤∑ _i : Fin b, p.1 :=
      Finset.sum_le_sum (fun i _ => min_le_left _ _)
    _ = b*p.1 := by simp

theorem polynomialSizeBound_le (b : ℕ) (p : Input) :
    polynomialSizeBound (totals b p)≤(capPolynomial b).eval p.1 := by
  rw [capPolynomial_eval]
  unfold polynomialSizeBound
  gcongr <;> exact total_sum_le b p

theorem exceptionalBound_le (b : ℕ) (p : Input) :
    exceptionalBound (CountVector (totals b p)) (totals b p)≤(capPolynomial b).eval p.1 :=
  (exceptionalBound_countVector_le (totals b p)).trans (polynomialSizeBound_le b p)

/-- The actual box enumerator may repeat clipped vectors; its larger pair
count is still bounded by the same fixed polynomial. -/
theorem boxExceptionalBound_le (b : ℕ) (p : Input) :
    exceptionalBound (Fin (ExponentVectors.box b p.1).length) (totals b p)≤
      (capPolynomial b).eval p.1 := by
  simp only [exceptionalBound,degreeBound,Fintype.card_fin,ExponentVectors.length_box,
    capPolynomial_eval]
  cases b with
  | zero => simp
  | succ b =>
    have hM : p.1≤(b+1)*p.1 := by nlinarith
    have hs := total_sum_le (b+1) p
    gcongr

/-- The automatic executable selector retains at least the requested count. -/
theorem length_candidates_ge (f : K →+* ℝ) (c a w : Fin b → K) (p : Input)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i))) :
    p.2.1≤(candidates c a w p).length := by
  exact BooleanNormSampleCompleteness.length_candidates_ge f c a w (prepare b p)
    ((capPolynomial b).eval p.1) p.2.1 rfl (boxExceptionalBound_le b p) hp

/-- Every retained rational is distinct because filtering preserves the
original grid's injectivity. -/
theorem nodup_candidates (c a w : Fin b → K) (p : Input) : (candidates c a w p).Nodup :=
  BooleanNormSampleSearch.nodup_candidates b (BooleanNormSampleMachines.bad c a w) (prepare b p)

/-- Explicit interval and reduced numerator/denominator bounds for the
actual values emitted by the machine. -/
theorem candidate_bounds (c a w : Fin b → K) (p : Input) (q : ℚ)
    (hq : q∈candidates c a w p) :
    (q : ℝ)∈Set.Ioo (0 : ℝ) 1 ∧ 0<q.num ∧
      q.num.natAbs≤(capPolynomial b).eval p.1+p.2.1 ∧
      0<q.den ∧ q.den≤(capPolynomial b).eval p.1+p.2.1+1 := by
  have hg := ((BooleanNormSampleMachines.mem_candidates_iff c a w (prepare b p) q).mp hq).1
  have h := BooleanExceptionalGrid.rationalGrid_num_den_bounds hg
  exact ⟨BooleanExceptionalGrid.rationalGrid_cast_mem_Ioo hg,h.1,h.2.1,q.den_pos,h.2.2⟩

/-- With a positive request, the actual first-candidate search cannot fall
through to its zero default. -/
theorem search_mem (f : K →+* ℝ) (c a w : Fin b → K) (p : Input)
    (hL : 0<p.2.1)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i))) :
    search c a w p∈candidates c a w p := by
  have hlen := length_candidates_ge f c a w p hp
  change (candidates c a w p).headD 0∈candidates c a w p
  cases heq : candidates c a w p with
  | nil => simp only [heq,List.length_nil] at hlen; omega
  | cons x xs => simp

/-- All honest bounded spectral-product families are separated, regardless
of their external indexing or repetitions. -/
theorem candidate_separates {I : Type*} (f : K →+* ℝ) (c a w : Fin b → K)
    (p : Input) (q : ℚ) (hq : q∈candidates c a w p)
    (k : I → Fin b → ℕ) (hk : ∀ i g, k i g≤totals b p g) :
    SeparatesUnequalCounts (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i))
      (totals b p) k (q : ℝ) :=
  BooleanNormSampleCompleteness.candidate_separates_bounded f c a w (prepare b p) q hq k hk

end PlanarHom.BooleanEffectiveSampling

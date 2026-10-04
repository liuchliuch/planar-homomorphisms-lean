import PlanarHom.DenseCoefficientSelection

/-! NEW: removing one extraneous transcendence variable from an arbitrary
dense fraction known to lie in the smaller rational-function field. The code
scans a nonzero denominator coefficient and retains matching coefficients. -/
noncomputable section
namespace PlanarHom.DenseOuterVariableDescent
open DensePolynomial DenseCoefficientSelection Complexity RepresentedBit

def polynomialBaseMap (d : ℕ) : Poly d →+* RationalFunction (d+1) :=
  (algebraMap (Poly (d+1)) (RationalFunction (d+1))).comp Polynomial.C

theorem polynomialBaseMap_injective (d : ℕ) : Function.Injective (polynomialBaseMap d) :=
  (IsFractionRing.injective (Poly (d+1)) (RationalFunction (d+1))).comp Polynomial.C_injective

def inclusion (d : ℕ) : RationalFunction d →+* RationalFunction (d+1) :=
  IsFractionRing.lift (polynomialBaseMap_injective d)

theorem inclusion_fractionValue (d : ℕ) (a : FractionCode d) :
    inclusion d (fractionValue d a) =
      algebraMap (Poly (d+1)) (RationalFunction (d+1)) (Polynomial.C (interpret d a.1)) /
      algebraMap (Poly (d+1)) (RationalFunction (d+1)) (Polynomial.C (interpret d a.2)) := by
  simp only [inclusion, fractionValue, map_div₀, IsFractionRing.lift_algebraMap,
    polynomialBaseMap, RingHom.comp_apply]
  rfl

theorem coefficient_ratio (d : ℕ) (a : FractionCode (d+1)) (ha : FractionValid (d+1) a)
    (c : FractionCode d) (hc : FractionValid d c)
    (h : fractionValue (d+1) a = inclusion d (fractionValue d c)) (k : ℕ)
    (hk : interpret d (coefficient d a.2 k) ≠ 0) :
    fractionValue d (coefficient d a.1 k,coefficient d a.2 k) = fractionValue d c := by
  have hs : algebraMap (Poly (d+1)) (RationalFunction (d+1))
      (Polynomial.C (interpret d c.2)) ≠ 0 := by
    exact fun hz => hc (Polynomial.C_injective
      ((IsFractionRing.injective (Poly (d+1)) (RationalFunction (d+1)))
        (by simpa only [map_zero] using hz)))
  rw [inclusion_fractionValue, fractionValue] at h
  have hcross := (div_eq_div_iff (denominator_ne_zero (d+1) a ha) hs).mp h
  let P : Polynomial (Poly d) := interpret (d+1) a.1
  let Q : Polynomial (Poly d) := interpret (d+1) a.2
  have hpq : P * Polynomial.C (interpret d c.2) =
      Polynomial.C (interpret d c.1) * Q := by
    apply IsFractionRing.injective (Poly (d+1)) (RationalFunction (d+1))
    simpa only [map_mul, P, Q] using hcross
  have hcoeff := congrArg (fun p : Polynomial (Poly d) => p.coeff k) hpq
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, P, Q, interpret_coeff] at hcoeff
  apply (div_eq_div_iff (denominator_ne_zero d (coefficient d a.1 k,coefficient d a.2 k) hk) (denominator_ne_zero d c hc)).mpr
  simpa only [fractionValue, ← map_mul, coefficient] using
    congrArg (algebraMap (Poly d) (RationalFunction d)) hcoeff

theorem descendFraction_value (d : ℕ) (a : FractionCode (d+1))
    (ha : FractionValid (d+1) a) (z : RationalFunction d)
    (hz : fractionValue (d+1) a = inclusion d z) :
    fractionValue d (descendFraction d a) = z := by
  obtain ⟨c,hc,rfl⟩ := fraction_complete d z
  have hp := pick_spec d a.2 ha
  have hk : coefficient d a.2 (pick d a.2).2 = (pick d a.2).1 := by
    simp only [coefficient,hp.1,Option.getD_some]
  have h := coefficient_ratio d a ha c hc hz (pick d a.2).2 (by rw [hk]; exact hp.2)
  simpa only [descendFraction,hk] using h

def descentProblem (d : ℕ) : Problem :=
  typedProblem (fractionEncoding (d+1)) (fractionEncoding d)
    (fun a => FractionValid (d+1) a ∧ ∃ z, fractionValue (d+1) a = inclusion d z)
    (fun a b => FractionValid d b ∧ inclusion d (fractionValue d b) = fractionValue (d+1) a)

/-- Exact prescribed smaller-field output, with charged ordinary bit cost,
for every valid representative satisfying the semantic subfield promise. -/
theorem descent_inFP (d : ℕ) : (descentProblem d).InFP := by
  apply typedProblem_inFP _ _ (fractionNormalizer (d+1)) _ _
    (descendFraction d) (fp_descendFraction d)
  intro a ha
  obtain ⟨z,hz⟩ := ha.2
  exact ⟨descendFraction_valid d a ha.1, by rw [descendFraction_value d a ha.1 z hz, hz]⟩

end PlanarHom.DenseOuterVariableDescent

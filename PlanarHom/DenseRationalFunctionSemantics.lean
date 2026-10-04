import PlanarHom.DensePolynomialProductSemantics
import Mathlib.RingTheory.Localization.FractionRing

/-! Noncanonical dense fraction pairs denote elements of the genuine fraction
field. Validity, every arithmetic operation and cross-product equality are
semantic facts; no gcd normalizer or abstract-field bit encoding is assumed. -/
noncomputable section
namespace PlanarHom.DensePolynomial

instance polyIsDomain : (n:ℕ)→IsDomain (Poly n)
  | 0 => inferInstanceAs (IsDomain ℚ)
  | n+1 => letI:=polyIsDomain n; inferInstanceAs (IsDomain (Polynomial (Poly n)))

abbrev RationalFunction (n:ℕ) := FractionRing (Poly n)

def FractionValid (n:ℕ) (a:FractionCode n) : Prop := interpret n a.2≠0

def fractionValue (n:ℕ) (a:FractionCode n) : RationalFunction n :=
  algebraMap (Poly n) (RationalFunction n) (interpret n a.1)/
    algebraMap (Poly n) (RationalFunction n) (interpret n a.2)

theorem denominator_ne_zero (n:ℕ) (a:FractionCode n) (ha:FractionValid n a) :
    algebraMap (Poly n) (RationalFunction n) (interpret n a.2)≠0 := by
  exact fun h=>ha ((IsFractionRing.to_map_eq_zero_iff).mp h)

theorem fractionMul_valid (n:ℕ) (a b:FractionCode n) (ha:FractionValid n a) (hb:FractionValid n b) :
    FractionValid n (fractionMul n a b) := by
  change interpret n (mul n a.2 b.2)≠0
  rw [interpret_mul]
  exact mul_ne_zero ha hb

theorem fractionAdd_valid (n:ℕ) (a b:FractionCode n) (ha:FractionValid n a) (hb:FractionValid n b) :
    FractionValid n (fractionAdd n a b) := fractionMul_valid n a b ha hb

theorem fractionNeg_valid (n:ℕ) (a:FractionCode n) (ha:FractionValid n a) :
    FractionValid n (fractionNeg n a) := ha

theorem fractionInv_valid (n:ℕ) (a:FractionCode n) (ha:fractionValue n a≠0) :
    FractionValid n (fractionInv n a) := by
  change interpret n a.1≠0
  intro h
  apply ha
  unfold fractionValue
  rw [h,map_zero,zero_div]

theorem fractionValue_mul (n:ℕ) (a b:FractionCode n) :
    fractionValue n (fractionMul n a b)=fractionValue n a*fractionValue n b := by
  simp only [fractionValue,fractionMul,interpret_mul,map_mul]
  symm
  exact div_mul_div_comm _ _ _ _

theorem fractionValue_add (n:ℕ) (a b:FractionCode n) (ha:FractionValid n a) (hb:FractionValid n b) :
    fractionValue n (fractionAdd n a b)=fractionValue n a+fractionValue n b := by
  simp only [fractionValue,fractionAdd,interpret_add,interpret_mul,map_mul,map_add]
  symm
  rw [div_add_div _ _ (denominator_ne_zero n a ha) (denominator_ne_zero n b hb)]
  congr 1
  ring

theorem fractionValue_neg (n:ℕ) (a:FractionCode n) :
    fractionValue n (fractionNeg n a)= -fractionValue n a := by
  simp only [fractionValue,fractionNeg,interpret_neg,map_neg]
  exact neg_div _ _

theorem fractionValue_inv (n:ℕ) (a:FractionCode n) :
    fractionValue n (fractionInv n a)=(fractionValue n a)⁻¹ := by
  simp [fractionValue,fractionInv]

/-- Exact equality on all valid representations, not equality of codewords. -/
theorem fractionEq_value_iff (n:ℕ) (a b:FractionCode n)
    (ha:FractionValid n a) (hb:FractionValid n b) :
    fractionEq n a b=true ↔ fractionValue n a=fractionValue n b := by
  rw [fractionEq_iff,fractionValue,fractionValue,
    div_eq_div_iff (denominator_ne_zero n a ha) (denominator_ne_zero n b hb)]
  constructor
  · intro h
    simpa only [map_mul] using congrArg (algebraMap (Poly n) (RationalFunction n)) h
  · intro h
    apply IsFractionRing.injective (Poly n) (RationalFunction n)
    simpa only [map_mul] using h

end PlanarHom.DensePolynomial

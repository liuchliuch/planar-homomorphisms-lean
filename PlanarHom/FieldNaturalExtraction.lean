import PlanarHom.FixedFieldEncodingTransport
import PlanarHom.ProperColoringNaturalReduction

/-! NEW actual field-to-natural extraction: a fixed rational-linear retraction
onto the rational subfield followed by binary numerator absolute value. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.FieldNaturalExtraction
open Complexity FixedFieldEncodingTransport ProperColoringPottsReduction
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

def rationalRetractionData (basis : Module.Basis (Fin dimension) ℚ K) :=
  exists_fp_leftInverse rationalBasis basis (Algebra.ofId ℚ K).toLinearMap (algebraMap ℚ K).injective

def rationalRetraction (basis : Module.Basis (Fin dimension) ℚ K) : K→ₗ[ℚ]ℚ :=
  Classical.choose (rationalRetractionData basis)

def extract (basis : Module.Basis (Fin dimension) ℚ K) (x : K) : ℕ := (rationalRetraction basis x).num.natAbs

theorem fp_extract (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (numberFieldEncoding basis) BitEncoding.nat (extract basis) :=
  (Classical.choose_spec (rationalRetractionData basis)).2.comp fp_extractNatural

theorem extract_natCast (basis : Module.Basis (Fin dimension) ℚ K) (n : ℕ) : extract basis (n:K)=n := by
  have h: rationalRetraction basis ((Algebra.ofId ℚ K) (n:ℚ))=(n:ℚ):=
    (Classical.choose_spec (rationalRetractionData basis)).1 (n:ℚ)
  simp only [map_natCast] at h
  simp only [extract,h,extractNatural_natCast]

end PlanarHom.FieldNaturalExtraction

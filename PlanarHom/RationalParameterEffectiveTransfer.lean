import PlanarHom.PresentedExtensionDegree
import PlanarHom.VariableDomainEffectiveTransfer

/-! Literal rational-parameter endpoints for source3.10. The subtype carries
only the mathematical promise x∈X; its word is exactly the original rational
word, so all uniform costs are measured in bit(x), not an arbitrary encoding. -/
noncomputable section
namespace PlanarHom.EffectiveProductTransfer
open Complexity
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {sourceDimension q bt ut dt : ℕ}

def rationalParameters (X : Set ℚ) : BitEncoding X := BitEncoding.rat.restrict (fun x => x ∈ X)

@[simp] theorem rationalParameters_encode (X : Set ℚ) (x : X) :
    (rationalParameters X).encode x = BitEncoding.rat.encode x.val := rfl

/-- Exact parameter-plus-raw-graph size, so presentation and entry FP hypotheses
are literally polynomial in rational bit length and original graph word length. -/
theorem rational_raw_input_length (X : Set ℚ) (x : X)
    (g : BitEncoding.ValidWord Complexity.MixedCode.encoding) :
    ((ParameterizedMatrixEvaluation.inputEncoding (rationalParameters X)).encode (x,g)).length =
      2 * (BitEncoding.rat.encode x.val).length + g.val.length + 1 :=
  BitEncoding.prod_length _ _ _

/-- Source3.10(P), variable fields, for x in the literal prescribed subset of Q. -/
def lemma310_polynomial_parameter (sourceBasis : Module.Basis (Fin sourceDimension) ℚ K₀)
    (X : Set ℚ) (fields : PresentedExtensions sourceBasis (rationalParameters X)) :=
  polynomial_variable_reduction (q:=q) (bt:=bt) (ut:=ut) sourceBasis (rationalParameters X) fields

/-- Source3.10(S), variable fields, for x in the literal prescribed subset of Q. -/
def lemma310_spectral_parameter (sourceBasis : Module.Basis (Fin sourceDimension) ℚ K₀)
    (X : Set ℚ) (fields : PresentedExtensions sourceBasis (rationalParameters X)) :=
  spectral_variable_reduction (q:=q) (bt:=bt) (ut:=ut) sourceBasis (rationalParameters X) fields

/-- The same polynomial transfer retaining every original domain assignment. -/
def lemma310_polynomial_domain_parameter (sourceBasis : Module.Basis (Fin sourceDimension) ℚ K₀)
    (X : Set ℚ) (fields : PresentedExtensions sourceBasis (rationalParameters X)) :=
  polynomial_variable_domain_reduction (q:=q) (bt:=bt) (ut:=ut) (dt:=dt)
    sourceBasis (rationalParameters X) fields

/-- The same spectral transfer retaining every original domain assignment. -/
def lemma310_spectral_domain_parameter (sourceBasis : Module.Basis (Fin sourceDimension) ℚ K₀)
    (X : Set ℚ) (fields : PresentedExtensions sourceBasis (rationalParameters X)) :=
  spectral_variable_domain_reduction (q:=q) (bt:=bt) (ut:=ut) (dt:=dt)
    sourceBasis (rationalParameters X) fields

end PlanarHom.EffectiveProductTransfer

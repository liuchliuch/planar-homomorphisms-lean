import PlanarHom.MixedEvaluationPromises
import PlanarHom.MixedTotalEvaluation
import PlanarHom.PrescribedDomainAliases

/-! The exact raw unary-parameter source problem used by uniform matrix-family simulation. -/
noncomputable section
namespace PlanarHom.DynamicMatrixFamilySource
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}

/-- Preserve every raw decoder word for unary n followed by the original graph codec. -/
def queryEncoding : BitEncoding (ℕ × MixedCode) := BitEncoding.unaryNat.prod MixedCode.encoding

def answer (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (p : ℕ × MixedCode) : K :=
  totalEvaluation (appendOne M (F p.1)) U w p.2

/-- Source (ii): one actual uniform promised problem, with n physically encoded
in unary and a valid ordinary planar graph over all original companion labels. -/
def problem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) : PromiseProblem :=
  ⟨fun raw => ∃ p : ℕ × MixedCode, queryEncoding.decode raw = some p ∧
      1 ≤ p.1 ∧ p.2.PlanarValid (bt + 1) ut,
    encodedFunction queryEncoding (numberFieldEncoding basis) (answer M U w F) []⟩

@[simp] theorem value_encode (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (p : ℕ × MixedCode) :
    (problem basis M U w F).value (queryEncoding.encode p) =
      (numberFieldEncoding basis).encode (answer M U w F p) :=
  encodedFunction_encode _ _ _ _ _

theorem encoded_valid (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (n : ℕ) (g : MixedCode)
    (hn : 1 ≤ n) (hg : g.PlanarValid (bt + 1) ut) :
    (problem basis M U w F).valid (queryEncoding.encode (n,g)) :=
  ⟨(n,g), queryEncoding.decode_encode _, hn, hg⟩

end PlanarHom.DynamicMatrixFamilySource

import PlanarHom.IsingInterpolationMachines
import PlanarHom.IsingRecoveredEvaluation
import PlanarHom.FixedRealCoefficientEvaluation
import PlanarHom.MixedTotalEvaluation
import PlanarHom.GraphCodeNormalization

/-! NEW actual fixed-real Ising evaluator via rational interpolation. Powers
and rational combinations use the bounded common-denominator program, never
an unreduced symbolic Horner loop. Arbitrary successful lexical input encodings
are normalized by the genuine graph codec machine. -/
noncomputable section
namespace PlanarHom.FixedRealIsingInterpolation
open Complexity DensePolynomial
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

 def program (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (g:MixedCode) :
    FixedRealExtension.Code n e :=
  FixedRealCoefficientEvaluation.evaluate basis ρ (IsingRationalInterpolation.planarCoefficients g)

 theorem fp_program (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) :
    FP MixedCode.encoding (FixedRealExtension.encoding n e) (program basis ρ) :=
  IsingRationalInterpolation.fp_planarCoefficients.comp (FixedRealCoefficientEvaluation.fp_evaluate basis ρ)

 theorem program_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (g:MixedCode) :
    FixedRealExtension.Valid n (program basis ρ g) :=
  FixedRealCoefficientEvaluation.evaluate_valid basis ρ _

 theorem program_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (f:ℚ→+*K) (ρ:K) (g:MixedCode) {bt ut:ℕ} (hp:g.PlanarValid bt ut) :
    FixedRealExtension.value basis (program basis ρ g)=
      (g.toMultiGraph hp.1).partition (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) := by
  rw [program,FixedRealCoefficientEvaluation.evaluate_coefficients basis f]
  exact IsingRationalInterpolation.planarCoefficients_value g hp f ρ

 def problem (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) : RepresentedBit.Problem :=
  (FixedRealExtension.presentation basis).problem MixedCode.encoding (MixedCode.PlanarValid 1 0)
    (MixedCode.totalEvaluation (fun _:Fin 1=>BooleanTensorEasyAssembly.isingMatrix ρ)
      (fun u:Fin 0=>u.elim0) (fun _=>1))

 theorem inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K) (ρ:K) :
    (problem basis ρ).InFP := by
  apply RepresentedBit.Presentation.problem_inFP _ _ MixedCode.normalizer _ _
    (program basis ρ) (fp_program basis ρ) (fun g _=>program_valid basis ρ g)
  intro g hp
  rw [MixedCode.totalEvaluation_valid _ _ _ g hp.1,MixedCode.evaluate_homogeneous]
  exact program_value basis f ρ g hp

end PlanarHom.FixedRealIsingInterpolation

import PlanarHom.RepresentedCanonicalRecovery
import PlanarHom.FixedRealIntegerExtraction
import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.AlgebraicProductInterpolation
import PlanarHom.FixedRealMixedInterpolation

/-! NEW: canonical answers for a fixed rational matrix are recovered from every
valid represented answer in an arbitrary prescribed RF-extension. The actual
trace/coefficient extractor is executed; no canonical oracle reply is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealApproximation
open DensePolynomial FixedRealExtension Complexity Complexity.MixedCode RepresentedBit
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
local instance : CharZero (RationalFunction n) := DenseRationalConstantExtraction.rationalFunction_charZero n

 def rationalLanguage (N : Matrix (Fin q) (Fin q) ℚ) : AlgebraicProductInterpolation.RealLanguage q 1 0 where
  matrices := fun _ i j => (N i j : ℝ)
  unaries := fun l => l.elim0
  weights := fun _ => 1
  matrices_algebraic := fun _ i j => isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (N i j)
  unaries_algebraic := fun l => l.elim0
  weights_algebraic := fun _ => isAlgebraic_one

 def rationalValue (N : Matrix (Fin q) (Fin q) ℚ) (g : MixedCode) : ℚ :=
  totalEvaluation (fun _ : Fin 1 => N) (fun l : Fin 0 => l.elim0) (fun _ => 1) g

 theorem rationalValue_cast {F : Type} [Field F] [CharZero F]
    (N : Matrix (Fin q) (Fin q) ℚ) (g : MixedCode) :
    (rationalValue N g : F) = totalEvaluation
      (fun _ : Fin 1 => fun i j => (N i j : F)) (fun l : Fin 0 => l.elim0) (fun _ => 1) g := by
  by_cases hg : g.Valid 1 0
  · simp only [rationalValue,totalEvaluation_valid _ _ _ g hg]
    have hu : (fun l : Fin 0 => fun i : Fin q => (((l.elim0 : Fin q → ℚ) i) : F)) =
        (fun l : Fin 0 => (l.elim0 : Fin q → F)) := by funext l; exact l.elim0
    simpa only [RingHom.coe_coe, Rat.coe_castHom, Rat.cast_one, hu] using map_evaluate (Rat.castHom F) g hg (fun _ : Fin 1 => N)
      (fun l : Fin 0 => l.elim0) (fun _ => (1 : ℚ))
  · simp [rationalValue,totalEvaluation,hg]

 theorem rationalLanguage_evaluate (N : Matrix (Fin q) (Fin q) ℚ) (g : MixedCode) (hg : g.Valid 1 0) :
    g.evaluate hg (rationalLanguage N).matricesK (rationalLanguage N).unariesK
      (rationalLanguage N).weightsK = (rationalValue N g : (rationalLanguage N).field) := by
  have hm : (rationalLanguage N).matricesK = fun _ : Fin 1 => fun i j => (N i j : (rationalLanguage N).field) := by
    funext l i j
    apply Subtype.ext
    rfl
  have hu : (rationalLanguage N).unariesK = fun l : Fin 0 => l.elim0 := by funext l; exact l.elim0
  have hw : (rationalLanguage N).weightsK = fun _ => 1 := by funext i; apply Subtype.ext; rfl
  rw [hm,hu,hw,rationalValue_cast,totalEvaluation_valid _ _ _ g hg]

 def rationalOracleDescent (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (N : Matrix (Fin q) (Fin q) ℚ) :
    Reduction (ofCanonical (rationalLanguage N).problem)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => (N i j : K))
        (fun l : Fin 0 => l.elim0) (fun _ => 1)) := by
  letI : CharZero K := Algebra.charZero_of_charZero (RationalFunction n) K
  let L := rationalLanguage N
  let target : MixedCode → Bits := fun g => (numberFieldEncoding L.basis).encode
    (rationalValue N g : L.field)
  let recover : Code n e → Bits := fun c => (numberFieldEncoding L.basis).encode
    (FixedRealIntegerExtraction.extractRational basis c : L.field)
  have hr : FP (encoding n e) BitEncoding.bits recover :=
    (((FixedRealIntegerExtraction.fp_extractRational basis).comp FixedRealIntegerExtraction.fp_rationalValue).comp
      (FixedFieldPolynomialMachines.fp_ratCast L.basis)).comp
      (fp_code_view (numberFieldEncoding L.basis) BitEncoding.bits (numberFieldEncoding L.basis).encode (fun _ => rfl))
  refine canonicalRecovery L.problem (presentation basis) MixedCode.encoding MixedCode.normalizer
    (MixedCode.PlanarValid 1 0) target _ (fun _ h => h) ?_ recover hr ?_
  · intro raw g hd hg
    change evaluationValue L.basis L.matricesK L.unariesK L.weightsK raw = _
    rw [evaluationValue_decode _ _ _ _ raw g hd hg.1,rationalLanguage_evaluate]
  · intro g hg c hc he
    have he' : value basis c = (rationalValue N g : K) := he.trans (rationalValue_cast N g).symm
    simp only [recover,FixedRealIntegerExtraction.extractRational_value basis c hc _ he']
    rfl

end PlanarHom.FixedRealApproximation

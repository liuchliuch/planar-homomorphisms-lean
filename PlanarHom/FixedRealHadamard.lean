import PlanarHom.SignedHadamardTractability
import PlanarHom.FixedRealGraphEvaluation
import PlanarHom.FixedRealRationalScaling
import PlanarHom.DenseRationalConstantExtraction

/-! NEW: the genuine rational Boolean-quadratic elimination algorithm is
lifted by an actual rational-to-prescribed-field code transformer. This uses
neither symbolic Gaussian elimination nor a field-value oracle. -/
noncomputable section
namespace PlanarHom.FixedRealSmallState
open Complexity Complexity.MixedCode DensePolynomial FixedRealExtension FixedRealGraphEvaluation
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

 def rationalLift (q : ℚ) : Code n e :=
  rationalScale n q (FixedRealCoefficientEvaluation.power basis (1 : K) 1)
 theorem fp_rationalLift : FP rationalCode (encoding n e) (rationalLift basis) :=
  ((fp_id rationalCode).pair (fp_const rationalCode (encoding n e)
    (FixedRealCoefficientEvaluation.power basis (1 : K) 1))).comp (fp_rationalScale n e)
 theorem rationalLift_valid (q : ℚ) : Valid n (rationalLift basis q) :=
  rationalScale_valid q _ (FixedRealCoefficientEvaluation.power_valid basis 1 1)
 theorem rationalLift_value (q : ℚ) : FixedRealExtension.value basis (rationalLift basis q) = (q : K) := by
  rw [rationalLift,rationalScale_value,FixedRealCoefficientEvaluation.power_value,one_pow,mul_one]

 def hadamardProgram (g : MixedCode) : Code n e := rationalLift basis (BooleanQuadratic.evaluate (K := ℚ) g)
 theorem fp_hadamardProgram : FP MixedCode.encoding (encoding n e) (hadamardProgram basis) :=
  (BooleanQuadratic.fp_evaluate rationalBasis).comp (fp_rationalLift basis)
 theorem hadamardProgram_valid (g : MixedCode) : Valid n (hadamardProgram basis g) := rationalLift_valid basis _

 theorem hadamardProgram_value (g : MixedCode) (hg : g.Valid 1 0) :
    FixedRealExtension.value basis (hadamardProgram basis g) =
      g.evaluate hg (fun _ : Fin 1 => SignedHadamard.interaction (K := K))
        BooleanTensorFPClosure.emptyUnaries (fun _ => 1) := by
  letI : CharZero (RationalFunction n) := DenseRationalConstantExtraction.rationalFunction_charZero n
  letI : CharZero K := Algebra.charZero_of_charZero (RationalFunction n) K
  rw [hadamardProgram,rationalLift_value,SignedHadamard.evaluate_eq g hg]
  have hm : (fun (_ : Fin 1) (i j : Bool) => (Rat.castHom K) (SignedHadamard.interaction (K := ℚ) i j)) =
      (fun _ : Fin 1 => SignedHadamard.interaction (K := K)) := by
    funext l i j
    cases i <;> cases j <;> norm_num [SignedHadamard.interaction,BooleanQuadratic.hadamard]
  have hu : (fun (u : Fin 0) (i : Bool) => (Rat.castHom K) (BooleanTensorFPClosure.emptyUnaries u i)) =
      (BooleanTensorFPClosure.emptyUnaries : Fin 0 → Bool → K) := by funext u; exact u.elim0
  have h := map_evaluate (Rat.castHom K) g hg
    (fun _ : Fin 1 => SignedHadamard.interaction (K := ℚ)) BooleanTensorFPClosure.emptyUnaries (fun _ => 1)
  rw [hm,hu] at h
  simpa only [map_one,Rat.coe_castHom] using h

 theorem hadamard : Evaluable basis (SignedHadamard.interaction (K := K)) (fun _ => 1) := by
  refine ⟨⟨hadamardProgram basis,fp_hadamardProgram basis,fun g _ => hadamardProgram_valid basis g,?_⟩⟩
  intro g hg
  rw [FixedRealGraphEvaluation.value,totalEvaluation_valid _ _ _ g hg.1]
  exact hadamardProgram_value basis g hg.1

end PlanarHom.FixedRealSmallState

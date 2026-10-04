import PlanarHom.FixedRealLinearMapMachines
import Mathlib.FieldTheory.NormalizedTrace

/-! NEW: actual normalized relative trace and prescribed-subfield output for
finite extensions over a common rational-function base. -/
noncomputable section
namespace PlanarHom.FixedRealTrace
open DensePolynomial FixedRealLinearMap Complexity RepresentedBit
variable {d e f : ℕ} {E F : Type} [Field E] [Field F] [CharZero F]
  [Algebra (RationalFunction d) E] [Algebra (RationalFunction d) F]
  [Algebra F E] [IsScalarTower (RationalFunction d) F E] [FiniteDimensional F E]

def traceMap : E →ₗ[RationalFunction d] F :=
  (Algebra.normalizedTrace F E).restrictScalars (RationalFunction d)

def run (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F) :
    FixedRealExtension.Code d e → FixedRealExtension.Code d f :=
  FixedRealLinearMap.run (table input output (traceMap (d := d)))

theorem fp_run (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F) :
    FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding d f) (run input output) :=
  FixedRealLinearMap.fp_run _

theorem run_valid (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (a : FixedRealExtension.Code d e) (ha : FixedRealExtension.Valid d a) :
    FixedRealExtension.Valid d (run input output a) := FixedRealLinearMap.run_valid _ a ha

theorem value_run (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (a : FixedRealExtension.Code d e) :
    FixedRealExtension.value output (run input output a) =
      Algebra.normalizedTrace F E (FixedRealExtension.value input a) :=
  FixedRealLinearMap.value_run _ input output _ (table_realizes input output _) a

/-- The original subfield element is recovered, rather than returned in an
auxiliary extension representation. Its value is not supplied to the machine. -/
theorem value_run_known (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (a : FixedRealExtension.Code d e) (z : F)
    (hz : FixedRealExtension.value input a = algebraMap F E z) :
    FixedRealExtension.value output (run input output a) = z := by
  rw [value_run, hz, Algebra.normalizedTrace_algebraMap_apply_eq_self F E z]

def descentProblem (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F) : Problem :=
  typedProblem (FixedRealExtension.encoding d e) (FixedRealExtension.encoding d f)
    (fun a => FixedRealExtension.Valid d a ∧
      ∃ z : F, FixedRealExtension.value input a = algebraMap F E z)
    (fun a b => FixedRealExtension.Valid d b ∧
      algebraMap F E (FixedRealExtension.value output b) = FixedRealExtension.value input a)

theorem descent_inFP (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F) : (descentProblem input output).InFP := by
  apply typedProblem_inFP _ _ (FixedRealExtension.normalizer d e) _ _
    (run input output) (fp_run input output)
  intro a ha
  obtain ⟨z,hz⟩ := ha.2
  exact ⟨run_valid input output a ha.1, by rw [value_run_known input output a z hz, hz]⟩

end PlanarHom.FixedRealTrace

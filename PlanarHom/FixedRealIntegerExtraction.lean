import PlanarHom.DenseRationalConstantExtraction
import PlanarHom.FixedRealTraceMachines

/-! NEW: ordinary rational/integer/natural output from a fixed RF-basis
presentation, using actual normalized trace and repeated coefficient scans.
The value-membership condition is a promise and supplies no value to the program. -/
noncomputable section
namespace PlanarHom.FixedRealIntegerExtraction
open DensePolynomial DenseRationalConstantExtraction Complexity PairProjectionMachines
variable {d e : ℕ} {E : Type} [Field E] [Algebra (RationalFunction d) E]
variable (basis : Module.Basis (Fin e) (RationalFunction d) E)
local instance : CharZero (RationalFunction d) := rationalFunction_charZero d

def scalarBasis (d : ℕ) : Module.Basis (Fin 1) (RationalFunction d) (RationalFunction d) :=
  Module.Basis.singleton (Fin 1) (RationalFunction d)

theorem scalarBasis_value (a : FixedRealExtension.Code d 1) :
    FixedRealExtension.value (scalarBasis d) a = fractionValue d (a.1 0,a.2) := by
  have h := (scalarBasis d).sum_equivFun (FixedRealExtension.value (scalarBasis d) a)
  simpa [scalarBasis,FixedRealExtension.value,FixedRealExtension.coordinates] using h.symm

def traceCode (a : FixedRealExtension.Code d e) : FixedRealExtension.Code d 1 := by
  letI : FiniteDimensional (RationalFunction d) E := Module.Finite.of_basis basis
  exact FixedRealTrace.run basis (scalarBasis d) a

def extractRational (a : FixedRealExtension.Code d e) : ℚ :=
  extract d ((traceCode basis a).1 0,(traceCode basis a).2)

theorem fp_extractRational : FP (FixedRealExtension.encoding d e) rationalCode (extractRational basis) := by
  letI : FiniteDimensional (RationalFunction d) E := Module.Finite.of_basis basis
  let ep := encoding d
  have ht := FixedRealTrace.fp_run basis (scalarBasis d)
  have hn := (fp_fst (ep.vector 1) ep).comp (FixedVectorMachines.fp_coordinate ep 1 0)
  exact (ht.comp (hn.pair (fp_snd (ep.vector 1) ep))).comp (fp_extract d)

theorem extractRational_value (a : FixedRealExtension.Code d e)
    (ha : FixedRealExtension.Valid d a) (q : ℚ)
    (hq : FixedRealExtension.value basis a = (q : E)) : extractRational basis a = q := by
  letI : FiniteDimensional (RationalFunction d) E := Module.Finite.of_basis basis
  have hr : (q : E) = algebraMap (RationalFunction d) E (constantMap d q) :=
    (eq_ratCast ((algebraMap (RationalFunction d) E).comp (constantMap d)) q).symm
  have ht := FixedRealTrace.value_run_known basis (scalarBasis d) a (constantMap d q) (hq.trans hr)
  rw [scalarBasis_value] at ht
  exact extract_value d ((traceCode basis a).1 0,(traceCode basis a).2)
    (FixedRealTrace.run_valid basis (scalarBasis d) a ha) q ht

def extractInteger (a : FixedRealExtension.Code d e) : ℤ := (extractRational basis a).num
def extractNatural (a : FixedRealExtension.Code d e) : ℕ := (extractInteger basis a).natAbs

theorem fp_rationalValue : FP rationalCode BitEncoding.rat id :=
  (FixedFieldArithmetic.fp_coordinate rationalBasis 0).congr (fun x => by
    simp [rationalBasis,Module.Basis.equivFun_apply])

theorem fp_extractInteger : FP (FixedRealExtension.encoding d e) BitEncoding.int (extractInteger basis) :=
  ((fp_extractRational basis).comp fp_rationalValue).comp ArithmeticCircuitPrimitives.fp_rat_num

theorem fp_extractNatural : FP (FixedRealExtension.encoding d e) BitEncoding.nat (extractNatural basis) :=
  (fp_extractInteger basis).comp ArithmeticCircuitPrimitives.fp_int_natAbs

theorem extractInteger_value (a : FixedRealExtension.Code d e)
    (ha : FixedRealExtension.Valid d a) (z : ℤ)
    (hz : FixedRealExtension.value basis a = (z : E)) : extractInteger basis a = z := by
  have h := extractRational_value basis a ha (z:ℚ) (by simpa using hz)
  simp only [extractInteger,h,Rat.num_intCast]

theorem extractNatural_value (a : FixedRealExtension.Code d e)
    (ha : FixedRealExtension.Valid d a) (n : ℕ)
    (hn : FixedRealExtension.value basis a = (n : E)) : extractNatural basis a = n := by
  have h := extractInteger_value basis a ha (n:ℤ) (by simpa using hn)
  simp only [extractNatural,h,Int.natAbs_natCast]

end PlanarHom.FixedRealIntegerExtraction

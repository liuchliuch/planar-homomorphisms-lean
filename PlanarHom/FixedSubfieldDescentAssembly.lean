import PlanarHom.FixedPresentationConversion
import PlanarHom.FixedRealVariableTowerDescent
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! NEW: the complete conversion/trace/coefficient program for a proved
compatible relative presentation. The remaining general existence theorem
constructs this semantic presentation data; no algorithm is assumed here. -/
noncomputable section
namespace PlanarHom.FixedSubfieldDescentAssembly
open DensePolynomial Complexity
variable {d e c f b : ℕ} {K F L : Type} [Field K] [Field F] [Field L] [CharZero L]
  [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F]
  [Algebra (RationalFunction (c+b)) L] [Algebra (RationalFunction (c+b)) K]
  [Algebra L K] [IsScalarTower (RationalFunction (c+b)) L K] [FiniteDimensional L K]
variable (source : Module.Basis (Fin e) (RationalFunction d) K)
  (target : Module.Basis (Fin f) (RationalFunction c) F)
  (auxiliary : Module.Basis (Fin f) (RationalFunction (c+b)) L)

def ambientBasis : Module.Basis (Fin (f * Module.finrank L K)) (RationalFunction (c+b)) K :=
  (auxiliary.smulTower (Module.finBasis L K)).reindex finProdFinEquiv

def prepare (a : FixedRealExtension.Code d e) :
    FixedRealExtension.Code (c+b) (f * Module.finrank L K) :=
  FixedPresentationConversion.run (ambientBasis (K := K) auxiliary) source (RingHom.id K) a

def trace (a : FixedRealExtension.Code d e) : FixedRealExtension.Code (c+b) f :=
  FixedRealTrace.run (ambientBasis (K := K) auxiliary) auxiliary (prepare source auxiliary a)

def run (a : FixedRealExtension.Code d e) : FixedRealExtension.Code c f :=
  FixedRealVariableTowerDescent.run c f b (trace source auxiliary a)

theorem fp_prepare : FP (FixedRealExtension.encoding d e)
    (FixedRealExtension.encoding (c+b) (f * Module.finrank L K)) (prepare source auxiliary) :=
  FixedPresentationConversion.fp_run _ source (RingHom.id K)

theorem fp_trace : FP (FixedRealExtension.encoding d e)
    (FixedRealExtension.encoding (c+b) f) (trace source auxiliary) :=
  (fp_prepare source auxiliary).comp (FixedRealTrace.fp_run _ auxiliary)

theorem fp_run : FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding c f)
    (run source auxiliary) :=
  (fp_trace source auxiliary).comp (FixedRealVariableTowerDescent.fp_run c f b)

theorem trace_valid (a : FixedRealExtension.Code d e) :
    FixedRealExtension.Valid (c+b) (trace source auxiliary a) :=
  FixedRealTrace.run_valid _ auxiliary _ (FixedPresentationConversion.run_valid _ source (RingHom.id K) a)

theorem run_valid (a : FixedRealExtension.Code d e) : FixedRealExtension.Valid c (run source auxiliary a) :=
  FixedRealVariableTowerDescent.run_valid c f b _ (trace_valid source auxiliary a)

theorem run_value (embed : F →+* L)
    (hcompat : FixedRealVariableTowerDescent.Compatible target auxiliary embed)
    (a : FixedRealExtension.Code d e) (z : F)
    (hz : FixedRealExtension.value source a = algebraMap L K (embed z)) :
    FixedRealExtension.value target (run source auxiliary a) = z := by
  have hp : FixedRealExtension.value (ambientBasis (K := K) auxiliary) (prepare source auxiliary a) =
      algebraMap L K (embed z) :=
    (FixedPresentationConversion.run_value _ source (RingHom.id K) a).trans hz
  have ht := FixedRealTrace.value_run_known (ambientBasis (K := K) auxiliary) auxiliary
    (prepare source auxiliary a) (embed z) hp
  exact FixedRealVariableTowerDescent.value_run_known target auxiliary embed hcompat
    (trace source auxiliary a) (trace_valid source auxiliary a) z ht

end PlanarHom.FixedSubfieldDescentAssembly

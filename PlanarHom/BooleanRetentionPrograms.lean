import PlanarHom.UnaryMarkedCount
import PlanarHom.BooleanInnerRecoveryProgram
import PlanarHom.BooleanEffectiveLengthSamples
import PlanarHom.ParameterizedPowerReduction
import PlanarHom.ListDropMachines
import PlanarHom.ListPrefixMachines
import PlanarHom.MaterializedPolynomialInterpolationMachines

/-! NEW actual sample-major graph-query and nested recovery programs for
Boolean class retention. All counts are explicit unary data where output
materialization needs them; arbitrary binary slice indices are safely clipped. -/
noncomputable section
namespace PlanarHom.BooleanRetentionPrograms
open Complexity Complexity.MixedCode PairProjectionMachines ArithmeticCircuitPrimitives
open BooleanInnerRecoveryProgram BooleanGroupedMetadataMachines
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b dimension : ℕ}

abbrev Query := ℚ×MixedCode
def queryEncoding : BitEncoding Query := BitEncoding.rat.prod encoding
abbrev Meta := ℕ×List ℚ
def metaEncoding : BitEncoding Meta := BitEncoding.unaryNat.prod BitEncoding.rat.list

def cap (selected : ℕ) (mult : Fin b→ℕ) (g : MixedCode) : ℕ :=
  queryCount mult (g.markedCount selected)

theorem fp_cap (selected : ℕ) (mult : Fin b→ℕ) : FP encoding BitEncoding.unaryNat (cap selected mult) :=
  (fp_unaryMarkedCount selected).comp (fp_queryCount mult)

/-- The clipped exponent agrees with its range index on every emitted query. -/
def queryAt (selected : ℕ) (mult : Fin b→ℕ) (p : Query×ℕ) : Query :=
  (p.1.1,p.1.2.stretchLabel selected selected (min (cap selected mult p.1.2) p.2))

theorem fp_queryAt (selected : ℕ) (mult : Fin b→ℕ) :
    FP (queryEncoding.prod BitEncoding.nat) queryEncoding (queryAt selected mult) := by
  have hp:=fp_fst queryEncoding BitEncoding.nat
  have hx:=hp.comp (fp_fst BitEncoding.rat encoding)
  have hg:=hp.comp (fp_snd BitEncoding.rat encoding)
  have hc:=hg.comp (fp_cap selected mult)
  have hk:=fp_snd queryEncoding BitEncoding.nat
  have hmin:=(hc.pair hk).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p=>min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  exact hx.pair ((hmin.pair hg).comp (fp_stretchLabel selected selected))

def innerQueries (selected : ℕ) (mult : Fin b→ℕ) (p : Query) : List Query :=
  (List.range (cap selected mult p.2)).map (fun k=>queryAt selected mult (p,k))

theorem fp_innerQueries (selected : ℕ) (mult : Fin b→ℕ) :
    FP queryEncoding queryEncoding.list (innerQueries selected mult) := by
  have hc:=(fp_snd BitEncoding.rat encoding).comp (fp_cap selected mult)
  have hr:=(hc.comp UnaryRangeMachines.fp_range).comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  exact (((fp_id queryEncoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext queryEncoding BitEncoding.nat queryEncoding
      _ (fp_queryAt selected mult))).congr (fun p=>by simp [innerQueries])

def prepare (selected : ℕ) (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b)
    (g : MixedCode) : Meta×List Query :=
  let m:=g.markedCount selected
  let xs:=BooleanEffectiveLengthSamples.samples c a w mult (mult g0) m
  ((m,xs),xs.flatMap (fun x=>innerQueries selected mult (x,g)))

theorem fp_prepare (basis : Module.Basis (Fin dimension) ℚ K) (selected : ℕ)
    (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) :
    FP encoding (metaEncoding.prod queryEncoding.list) (prepare selected c a w mult g0) := by
  have hm:=fp_unaryMarkedCount selected
  have hx:=hm.comp (BooleanEffectiveLengthSamples.fp_samples basis c a w mult (mult g0))
  have hrow:=( (fp_snd encoding BitEncoding.rat).pair (fp_fst encoding BitEncoding.rat)).comp
    (fp_innerQueries selected mult)
  have hqs:=(((fp_id encoding).pair hx).comp
    (ListContextMachines.fp_mapWithContext encoding BitEncoding.rat queryEncoding.list
      (fun p=>innerQueries selected mult (p.2,p.1)) hrow)).comp
    (ListFlattenMachines.fp_flatten queryEncoding)
  exact ((hm.pair hx).pair hqs).congr (fun g=>by simp [prepare,List.flatMap_def])

def answerBlock (mult : Fin b→ℕ) (p : (Meta×List K)×ℕ) : List K :=
  (p.1.2.drop (p.2*queryCount mult p.1.1.1)).take (queryCount mult p.1.1.1)

theorem fp_answerBlock (basis : Module.Basis (Fin dimension) ℚ K) (mult : Fin b→ℕ) :
    FP ((metaEncoding.prod (numberFieldEncoding basis).list).prod BitEncoding.nat)
      (numberFieldEncoding basis).list (answerBlock mult) := by
  let ef:=numberFieldEncoding basis
  let ec:=metaEncoding.prod ef.list
  have hp:=fp_fst ec BitEncoding.nat
  have hm:=(hp.comp (fp_fst metaEncoding ef.list)).comp
    (fp_fst BitEncoding.unaryNat BitEncoding.rat.list)
  have hn:=(hm.comp (fp_queryCount mult)).comp UnaryNatConversionMachine.fp_conversion
  have hi:=fp_snd ec BitEncoding.nat
  have hs:=(hi.pair hn).comp BinaryArithmetic.fp_multiplication
  have hy:=hp.comp (fp_snd metaEncoding ef.list)
  have hd:=(hs.pair hy).comp (ListDropMachines.fp_drop ef 0)
  exact (hd.pair hn).comp (ListPrefixMachines.fp_take ef)

def recoveryRow (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b)
    (p : (Meta×List K)×(ℚ×ℕ)) : K×K :=
  (algebraMap ℚ K p.2.1,
    recover c a w mult g0 ((p.1.1.1,p.2.1),answerBlock mult (p.1,p.2.2)))

theorem fp_recoveryRow (basis : Module.Basis (Fin dimension) ℚ K)
    (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) :
    FP ((metaEncoding.prod (numberFieldEncoding basis).list).prod
      (BitEncoding.rat.prod BitEncoding.nat))
      ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) (recoveryRow c a w mult g0) := by
  let ef:=numberFieldEncoding basis
  let ec:=metaEncoding.prod ef.list
  have hp:=fp_fst ec (BitEncoding.rat.prod BitEncoding.nat)
  have hx:=(fp_snd ec (BitEncoding.rat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.rat BitEncoding.nat)
  have hi:=(fp_snd ec (BitEncoding.rat.prod BitEncoding.nat)).comp
    (fp_snd BitEncoding.rat BitEncoding.nat)
  have hm:=(hp.comp (fp_fst metaEncoding ef.list)).comp
    (fp_fst BitEncoding.unaryNat BitEncoding.rat.list)
  have hb:=(hp.pair hi).comp (fp_answerBlock basis mult)
  have hv:=((hm.pair hx).pair hb).comp (BooleanInnerRecoveryProgram.fp_recover basis c a w mult g0)
  exact (hx.comp (FixedFieldPolynomialMachines.fp_ratCast basis)).pair hv

def recoveryTable (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b)
    (p : Meta×List K) : List (K×K) :=
  p.1.2.zipIdx.map (fun x=>recoveryRow c a w mult g0 (p,x))

theorem fp_recoveryTable (basis : Module.Basis (Fin dimension) ℚ K)
    (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) :
    FP (metaEncoding.prod (numberFieldEncoding basis).list)
      (((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list)
      (recoveryTable c a w mult g0) := by
  let ef:=numberFieldEncoding basis
  let ec:=metaEncoding.prod ef.list
  have hx:=(fp_fst metaEncoding ef.list).comp (fp_snd BitEncoding.unaryNat BitEncoding.rat.list)
  have hi:=hx.comp (ListIndexMachines.fp_zipIdx BitEncoding.rat)
  exact ((fp_id ec).pair hi).comp
    (ListContextMachines.fp_mapWithContext ec (BitEncoding.rat.prod BitEncoding.nat)
      (ef.prod ef) _ (fp_recoveryRow basis c a w mult g0))

def recoverFinal (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) (x0 : K)
    (p : Meta×List K) : K :=
  MaterializedPolynomialInterpolationMachines.recover x0 (recoveryTable c a w mult g0 p)

theorem fp_recoverFinal (basis : Module.Basis (Fin dimension) ℚ K)
    (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) (x0 : K) :
    FP (metaEncoding.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis)
      (recoverFinal c a w mult g0 x0) :=
  (fp_recoveryTable basis c a w mult g0).comp
    (MaterializedPolynomialInterpolationMachines.fp_recover basis x0)

end PlanarHom.BooleanRetentionPrograms

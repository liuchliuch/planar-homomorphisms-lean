import PlanarHom.PottsCenteredPolynomial
import PlanarHom.MaterializedPolynomialCoefficientMachines
import PlanarHom.MaterializedPowerMachines
import PlanarHom.GraphInterpolationQueries
import PlanarHom.FixedPowerMachines
import PlanarHom.MixedUnaryParallelMachines

/-! NEW reconstruction: literal parallel-query and rational recovery programs
for a requested centered coefficient. Only the requested coefficient uses a
binary index; graph dimensions and all power-loop counts are honestly unary. -/
noncomputable section
open Classical
namespace PlanarHom.PottsCoefficientPrograms
open Complexity Complexity.MixedCode PairProjectionMachines
open ProperColoringPottsReduction PottsCentered

abbrev Meta := ℕ × (ℕ × ℕ)
abbrev Post := Meta × List ℚ
abbrev Input := ℕ × MixedCode

def basis := rationalBasis
def fieldCode := numberFieldEncoding basis
def metaEncoding := BitEncoding.nat.prod (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
def inputEncoding := BitEncoding.nat.prod MixedCode.encoding
def postEncoding := metaEncoding.prod fieldCode.list

def queries (g : MixedCode) : List MixedCode :=
  GraphInterpolationQueries.queries (MixedCode.parallelLabel 0) (g.edges.length+1,g)

def prepare (p : Input) : Meta × List MixedCode :=
  ((p.1,(p.2.vertices,p.2.edges.length)),queries p.2)

def row (q : ℕ) (p : Post) (i : ℕ) : ℚ × ℚ :=
  let k:=min (p.1.2.2+1) (i+1)
  (sampleNode q k,(q:ℚ)⁻¹^p.1.2.1*(sampleScale q k)^p.1.2.2*p.2.getD i 0)

def table (q : ℕ) (p : Post) : List (ℚ × ℚ) :=
  (List.range (p.1.2.2+1)).map (row q p)

def recover (q : ℕ) (p : Post) : ℚ :=
  MaterializedPolynomialCoefficientMachines.recover (p.1.1,table q p)

def coefficientValue (q : ℕ) (p : Input) : ℚ :=
  if h : p.2.Valid 1 0 then (polynomial (p.2.toMultiGraph h) q).coeff p.1 else 0

theorem fp_prepare : FP inputEncoding (metaEncoding.prod MixedCode.encoding.list) prepare := by
  have hd := fp_fst BitEncoding.nat MixedCode.encoding
  have hg := fp_snd BitEncoding.nat MixedCode.encoding
  have hn := hg.comp MixedCode.fp_vertices
  have hm := (hg.comp MixedCode.fp_edges).comp (ListUnaryLengthMachine.fp_length _)
  have hsize := (hm.pair (fp_const inputEncoding BitEncoding.unaryNat 1)).comp
    UnaryPolynomialMachines.fp_add
  have hqueries := (hsize.pair hg).comp (GraphInterpolationQueries.fp_binaryQueries 0)
  exact (hd.pair (hn.pair hm)).pair hqueries

theorem fp_row (q : ℕ) : FP (postEncoding.prod BitEncoding.nat) (fieldCode.prod fieldCode)
    (fun p => row q p.1 p.2) := by
  let inp := postEncoding.prod BitEncoding.nat
  have hp := fp_fst postEncoding BitEncoding.nat
  have hi := fp_snd postEncoding BitEncoding.nat
  have hm0 := hp.comp (fp_fst metaEncoding fieldCode.list)
  have hnm := hm0.comp (fp_snd BitEncoding.nat (BitEncoding.unaryNat.prod BitEncoding.unaryNat))
  have hn := hnm.comp (fp_fst BitEncoding.unaryNat BitEncoding.unaryNat)
  have hm := hnm.comp (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat)
  have ha := hp.comp (fp_snd metaEncoding fieldCode.list)
  have hmp := (hm.pair (fp_const inp BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add
  have hip := hi.comp BinaryArithmetic.fp_successor
  have hk := (hmp.pair hip).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  have htwo := hk.comp (FixedPowerMachines.fp_power basis (2:ℚ))
  have hq := fp_const inp fieldCode (q:ℚ)
  have hone := fp_const inp fieldCode (1:ℚ)
  have hnum := (htwo.pair hone).comp (FixedFieldArithmetic.fp_subtraction basis)
  have hden := (((htwo.pair hq).comp (FixedFieldArithmetic.fp_addition basis)).pair hone).comp
    (FixedFieldArithmetic.fp_subtraction basis)
  have hx := (hnum.pair hden).comp (FixedFieldArithmetic.fp_division basis)
  have hs := (hq.pair hden).comp (FixedFieldArithmetic.fp_division basis)
  have hpow := (hm.pair hs).comp (MaterializedPowerMachines.fp_power basis)
  have hnorm := hn.comp (FixedPowerMachines.fp_power basis ((q:ℚ)⁻¹))
  have hget := (hi.pair ha).comp (MaterializedPolynomialCoefficientMachines.fp_coefficientLookup basis)
  have hfactor := (hnorm.pair hpow).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact hx.pair ((hfactor.pair hget).comp (FixedFieldArithmetic.fp_multiplication basis))

theorem fp_table (q : ℕ) : FP postEncoding (fieldCode.prod fieldCode).list (table q) := by
  have hp := fp_fst metaEncoding fieldCode.list
  have hnm := hp.comp (fp_snd BitEncoding.nat (BitEncoding.unaryNat.prod BitEncoding.unaryNat))
  have hm := hnm.comp (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat)
  have hsize := (hm.pair (fp_const postEncoding BitEncoding.unaryNat 1)).comp
    UnaryPolynomialMachines.fp_add
  have hrange := (UnaryRangeMachines.fp_range.comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n => List.reverse_reverse (List.range n))
  have hr := hsize.comp hrange
  exact ((fp_id postEncoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext postEncoding BitEncoding.nat (fieldCode.prod fieldCode)
      (fun p => row q p.1 p.2) (fp_row q))

/-- All powers, answer lookups, sample pairs and coefficient extraction are
computed by actual machines on total inputs; no answer-size premise is used. -/
theorem fp_recover (q : ℕ) : FP postEncoding fieldCode (recover q) := by
  have hd := (fp_fst metaEncoding fieldCode.list).comp
    (fp_fst BitEncoding.nat (BitEncoding.unaryNat.prod BitEncoding.unaryNat))
  exact (hd.pair (fp_table q)).comp (MaterializedPolynomialCoefficientMachines.fp_recover basis)
end PlanarHom.PottsCoefficientPrograms

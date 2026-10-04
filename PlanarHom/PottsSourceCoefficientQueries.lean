import PlanarHom.PottsInheritedParallelRows
import PlanarHom.GraphInterpolationQueries
import PlanarHom.BoundedUnaryMachines

/-! NEW literal row-major radial query batch. Both dimensions are derived
from the materialized source graph. Binary loop indices are clamped against
those unary bounds before any expansion, so the program is FP on every input. -/
namespace PlanarHom.PottsSourceCoefficientQueries
open Complexity PairProjectionMachines PottsSourceInverseRows
abbrev Data := MixedCode×Rows
abbrev dataCode := PottsSourceInverseRows.inputCode
abbrev queryCode := PottsCoefficientPrograms.inputEncoding
abbrev sampleCode := dataCode.prod (BitEncoding.unaryNat.prod BitEncoding.unaryNat)

def width (d : Data) : ℕ := d.1.edges.length+1

def sample (d : Data) (k t : ℕ) : ℕ×MixedCode :=
  RadialPotts.Numeric.coefficientQuery
    (radialInput (d.1.parallelLabel 0 t) (parallelRows t d.2) k)

def indexedSample (d : Data) (i : ℕ) : ℕ×MixedCode :=
  sample d (min d.1.vertices (i/width d+1)) (min (width d) (i%width d+1))

def queries (d : Data) : List (ℕ×MixedCode) :=
  (List.range (d.1.vertices*width d)).map (indexedSample d)

theorem fp_width : FP dataCode BitEncoding.unaryNat width := by
  have hm:=(fp_fst MixedCode.encoding rowsCode).comp fp_edgeCountUnary
  exact (hm.pair (fp_const dataCode BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add

theorem fp_sample : FP sampleCode queryCode (fun p=>sample p.1 p.2.1 p.2.2) := by
  have hc:=fp_fst dataCode (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
  have hkt:=fp_snd dataCode (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
  have hk:=hkt.comp (fp_fst BitEncoding.unaryNat BitEncoding.unaryNat)
  have ht:=hkt.comp (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat)
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hparallel:=(ht.pair hg).comp (MixedParallelMachines.fp_parallelLabel 0)
  have hrows:=(ht.pair hrs).comp fp_parallelRows
  exact ((hparallel.pair hrows).pair hk).comp PottsSourceInverseRows.fp_coefficientQuery

theorem fp_indexedSample : FP (dataCode.prod BitEncoding.nat) queryCode
    (fun p=>indexedSample p.1 p.2) := by
  let inp:=dataCode.prod BitEncoding.nat
  have hd:=fp_fst dataCode BitEncoding.nat
  have hi:=fp_snd dataCode BitEncoding.nat
  have hw:=hd.comp fp_width
  have hwb:=hw.comp UnaryNatConversionMachine.fp_conversion
  have hdivision:=(hi.pair hwb).comp BinaryArithmetic.fp_division
  have hk:=(hdivision.comp (fp_fst BitEncoding.nat BitEncoding.nat)).comp BinaryArithmetic.fp_successor
  have ht:=(hdivision.comp (fp_snd BitEncoding.nat BitEncoding.nat)).comp BinaryArithmetic.fp_successor
  have hn:=(hd.comp (fp_fst MixedCode.encoding rowsCode)).comp MixedCode.fp_vertices
  have hbound : FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p=>min p.1 p.2) := ⟨BoundedUnaryMachines.computer⟩
  have hkb:=(hn.pair hk).comp hbound
  have htb:=(hw.pair ht).comp hbound
  exact (hd.pair (hkb.pair htb)).comp fp_sample

theorem fp_queries : FP dataCode queryCode.list queries := by
  have hn:=(fp_fst MixedCode.encoding rowsCode).comp MixedCode.fp_vertices
  have hsize:=(hn.pair fp_width).comp UnaryPolynomialMachines.fp_mul
  have hr:=hsize.comp UnaryArithmeticMachines.fp_range
  exact ((fp_id dataCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext dataCode BitEncoding.nat queryCode _ fp_indexedSample)

theorem indexedSample_row_major (d : Data) (k l : ℕ)
    (hk : k<d.1.vertices) (hl : l<width d) :
    indexedSample d (k*width d+l)=sample d (k+1) (l+1) := by
  have hw : 0<width d := by simp [width]
  have hdiv : (k*width d+l)/width d=k := by
    rw [Nat.mul_comm k (width d), Nat.mul_add_div hw, Nat.div_eq_of_lt hl, Nat.add_zero]
  have hmod : (k*width d+l)%width d=l := by simp [Nat.add_mod,Nat.mod_eq_of_lt hl]
  simp only [indexedSample,hdiv,hmod,min_eq_right (by omega : k+1≤d.1.vertices),
    min_eq_right (by omega : l+1≤width d)]

@[simp] theorem queries_length (d : Data) : (queries d).length=d.1.vertices*width d := by simp [queries]

theorem getD_answers_row_major (d : Data) (answer : (ℕ×MixedCode)→ℚ)
    (k l : ℕ) (hk : k<d.1.vertices) (hl : l<width d) :
    ((queries d).map answer).getD (k*width d+l) 0=answer (sample d (k+1) (l+1)) := by
  have hi : k*width d+l<d.1.vertices*width d := by nlinarith
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [queries,List.getElem_map,List.getElem_range]
  rw [indexedSample_row_major d k l hk hl]

end PlanarHom.PottsSourceCoefficientQueries

import PlanarHom.SelectedStretchCode
import PlanarHom.ListIndexMachines
import PlanarHom.ListReverseMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.ListDecompositionMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.MixedRelabelMachines
import PlanarHom.BinaryMultiplicationMachine

/-! Actual typed and raw ordinary TM2 compilation of selected-label paths. The
path parameter is unary. Endpoints and labels use the existing binary codec. -/

namespace PlanarHom.UnaryArithmeticMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

theorem fp_add : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
    BitEncoding.unaryNat (fun p => p.1+p.2) := by
  have hv := fp_code_view BitEncoding.unaryNat BitEncoding.bits
    BitEncoding.unaryNat.encode (fun _ => rfl)
  have hl := (fp_fst BitEncoding.unaryNat BitEncoding.unaryNat).comp hv
  have hr := (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat).comp hv
  apply ((hl.pair hr).comp PairProjectionMachines.fp_append).transportOutput
  intro p
  change Computability.unaryEncodeNat p.1 ++ Computability.unaryEncodeNat p.2 =
    Computability.unaryEncodeNat (p.1+p.2)
  induction p.1 with
  | zero => simp only [Computability.unaryEncodeNat, Nat.zero_add, List.nil_append]
  | succ n ih =>
    simpa only [Computability.unaryEncodeNat, Nat.succ_add, List.cons_append] using
      congrArg (List.cons true) ih

theorem fp_succ : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n => n+1) :=
  ((fp_id BitEncoding.unaryNat).pair (fp_const BitEncoding.unaryNat BitEncoding.unaryNat 1)).comp fp_add

theorem fp_range : FP BitEncoding.unaryNat BitEncoding.nat.list List.range := by
  exact (UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
    (fun _ => List.reverse_reverse _)

theorem fp_pred : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n => n-1) := by
  exact ((fp_range.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)).comp
    (ListUnaryLengthMachine.fp_length BitEncoding.nat)).congr (fun n => by simp)

theorem fp_mul : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
    BitEncoding.unaryNat (fun p => p.1*p.2) := by
  let e := BitEncoding.nat
  have hl := (fp_fst BitEncoding.unaryNat BitEncoding.unaryNat).comp fp_range
  have hr := (fp_snd BitEncoding.unaryNat BitEncoding.unaryNat).comp fp_range
  have hm := ListContextMachines.fp_mapWithContext e.list e e.list
    (fun p => p.1) (fp_fst e.list e)
  have hf := ((hl.pair hr).comp hm).comp (ListFlattenMachines.fp_flatten e)
  exact (hf.comp (ListUnaryLengthMachine.fp_length e)).congr (fun p => by
    simp [List.length_flatten, Function.comp_def, Nat.mul_comm])

end PlanarHom.UnaryArithmeticMachines

namespace PlanarHom.Complexity.MixedCode
open PairProjectionMachines BinaryArithmetic

private abbrev edgeItem := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
private abbrev indexedEdge := edgeItem.prod BitEncoding.nat
private abbrev binaryContext := BitEncoding.nat.prod (BitEncoding.nat.prod indexedEdge)
private abbrev pathContext := BitEncoding.unaryNat.prod BitEncoding.unaryNat

private theorem fp_pathSegment (replacement : ℕ) :
    FP (binaryContext.prod BitEncoding.nat) edgeItem
      (fun p => pathSegment p.1.1 replacement p.1.2.1 p.1.2.2 p.2) := by
  let n := BitEncoding.nat
  have hc := fp_fst binaryContext n
  have hv := hc.comp (fp_fst n (n.prod indexedEdge))
  have hrest := hc.comp (fp_snd n (n.prod indexedEdge))
  have hn := hrest.comp (fp_fst n indexedEdge)
  have he := hrest.comp (fp_snd n indexedEdge)
  have hedge := he.comp (fp_fst edgeItem n)
  have hi := he.comp (fp_snd edgeItem n)
  have hsrc := hedge.comp (fp_fst n (n.prod n))
  have hdst := (hedge.comp (fp_snd n (n.prod n))).comp (fp_fst n n)
  have hk := fp_snd binaryContext n
  have hbase := (hv.pair ((hi.pair hn).comp fp_multiplication)).comp fp_addition
  have hkm := (hk.pair (fp_const (binaryContext.prod n) n 1)).comp fp_subtraction
  have hnewsrc := (hbase.pair hkm).comp fp_addition
  have hnewdst := (hbase.pair hk).comp fp_addition
  have hzero := (hk.pair (fp_const (binaryContext.prod n) n 0)).comp NatListSumMachines.fp_equal
  have hlast := (hk.pair hn).comp NatListSumMachines.fp_equal
  exact (hzero.ite hsrc hnewsrc).pair
    ((hlast.ite hdst hnewdst).pair (fp_const (binaryContext.prod n) n replacement))

private theorem fp_pathList (replacement : ℕ) :
    FP (pathContext.prod indexedEdge) edgeItem.list
      (fun p => pathList p.1.1 replacement p.1.2 p.2) := by
  let u := BitEncoding.unaryNat
  let n := BitEncoding.nat
  have hc := fp_fst pathContext indexedEdge
  have hv := (hc.comp (fp_fst u u)).comp UnaryNatConversionMachine.fp_conversion
  have hnu := hc.comp (fp_snd u u)
  have hn := hnu.comp UnaryNatConversionMachine.fp_conversion
  have he := fp_snd pathContext indexedEdge
  have hcontext := hv.pair (hn.pair he)
  have hrange := (hnu.comp UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
  exact (hcontext.pair hrange).comp
    (ListContextMachines.fp_mapWithContext binaryContext n edgeItem
      (fun p => pathSegment p.1.1 replacement p.1.2.1 p.1.2.2 p.2)
      (fp_pathSegment replacement))

private theorem fp_label_test (selected : ℕ) :
    FP edgeItem BitEncoding.bool (fun e => decide (e.2.2=selected)) := by
  let n := BitEncoding.nat
  have hl := (fp_snd n (n.prod n)).comp (fp_snd n n)
  exact (hl.pair (fp_const edgeItem n selected)).comp NatListSumMachines.fp_equal

theorem fp_selectedEdges (selected : ℕ) : FP encoding edgeEncoding (fun g => g.selectedEdges selected) :=
  fp_edges.comp (ListFilterMachines.fp_filter edgeItem _ (fp_label_test selected))

theorem fp_companionEdges (selected : ℕ) : FP encoding edgeEncoding (fun g => g.companionEdges selected) := by
  have hp : FP edgeItem BitEncoding.bool (fun e => decide (e.2.2≠selected)) :=
    ((fp_label_test selected).comp
      (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool Bool.not)).congr
        (fun e => by simp)
  exact fp_edges.comp (ListFilterMachines.fp_filter edgeItem _ hp)

/-- A genuine ordinary polynomial-time machine for the exact existing mixed
codec. The size argument is `n` in unary and the original mixed codeword. -/
theorem fp_stretchLabel (selected replacement : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding
      (fun p => p.2.stretchLabel selected replacement p.1) := by
  let input := BitEncoding.unaryNat.prod encoding
  have hn := fp_fst BitEncoding.unaryNat encoding
  have hg := fp_snd BitEncoding.unaryNat encoding
  have hv := hg.comp fp_vertices
  have hs := hg.comp (fp_selectedEdges selected)
  have hcount := hs.comp (ListUnaryLengthMachine.fp_length edgeItem)
  have hnew := (hcount.pair hn).comp UnaryArithmeticMachines.fp_mul
  have hvOut := (hv.pair hnew).comp UnaryArithmeticMachines.fp_add
  have hindex := hs.comp (ListIndexMachines.fp_zipIdx edgeItem)
  have hpaths := (((hv.pair hn).pair hindex).comp
    (ListContextMachines.fp_mapWithContext pathContext indexedEdge edgeItem.list
      (fun p => pathList p.1.1 replacement p.1.2 p.2) (fp_pathList replacement))).comp
        (ListFlattenMachines.fp_flatten edgeItem)
  have hcomp := hg.comp (fp_companionEdges selected)
  have hedges := (hpaths.pair hcomp).comp (ListMutationMachines.fp_append edgeItem)
  have hout := hvOut.pair (hedges.pair (hg.comp fp_unaries))
  apply hout.transportOutput
  intro p
  change (BitEncoding.unaryNat.prod (edgeEncoding.prod unaryEncoding)).encode
    (p.2.vertices+(p.2.selectedEdges selected).length*p.1,
      ((p.2.selectedEdges selected).zipIdx.map (pathList p.2.vertices replacement p.1)).flatten ++
        p.2.companionEdges selected,p.2.unaries) = _
  simp only [encoding, BitEncoding.retract, stretchLabel_vertices,
    stretchLabel_edges_eq_flatMap, stretchLabel_unaries, List.flatMap]
  rfl

noncomputable def stretchLabelComputer (selected replacement : ℕ) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod encoding).toFinEncoding
      encoding.toFinEncoding (fun p => p.2.stretchLabel selected replacement p.1) :=
  Classical.choice (fp_stretchLabel selected replacement)

/-- The paper's positive path length, with a total length-one fallback at zero. -/
def stretchLabelLength (g : MixedCode) (selected replacement h : ℕ) : MixedCode :=
  g.stretchLabel selected replacement (h-1)

theorem fp_stretchLabelLength (selected replacement : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding
      (fun p => p.2.stretchLabelLength selected replacement p.1) :=
  ((((fp_fst BitEncoding.unaryNat encoding).comp UnaryArithmeticMachines.fp_pred).pair
    (fp_snd BitEncoding.unaryNat encoding)).comp (fp_stretchLabel selected replacement))

noncomputable def stretchLabelLengthComputer (selected replacement : ℕ) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod encoding).toFinEncoding
      encoding.toFinEncoding (fun p => p.2.stretchLabelLength selected replacement p.1) :=
  Classical.choice (fp_stretchLabelLength selected replacement)

noncomputable def stretchLabelLengthRawComputer (selected replacement : ℕ) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding
      (fun w => w.value.2.stretchLabelLength selected replacement w.value.1) :=
  MachineComposition.composeComputers
    (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (stretchLabelLengthComputer selected replacement)

noncomputable def stretchLabelLength_raw_outputs (selected replacement : ℕ) (raw : Bits)
    (h : ℕ) (g : MixedCode) (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (h,g)) :
    Turing.TM2OutputsInTime (stretchLabelLengthRawComputer selected replacement).tm
      (raw.map (stretchLabelLengthRawComputer selected replacement).inputAlphabet.symm)
      (some ((encoding.encode (g.stretchLabelLength selected replacement h)).map
        (stretchLabelLengthRawComputer selected replacement).outputAlphabet.symm))
      ((stretchLabelLengthRawComputer selected replacement).time.eval raw.length) := by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding) := ⟨raw,⟨(h,g),hd⟩⟩
  have hv : w.value=(h,g) := BitEncoding.ValidWord.value_eq hd
  have hout := (stretchLabelLengthRawComputer selected replacement).outputsFun w
  simpa only [BitEncoding.toFinEncoding, BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw, w, hv] using hout

/-- The normalizer reads every successfully decoded raw parameter/graph pair;
the compiler is therefore not restricted to canonical input codewords. -/
noncomputable def stretchLabelRawComputer (selected replacement : ℕ) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding
      (fun w => w.value.2.stretchLabel selected replacement w.value.1) :=
  MachineComposition.composeComputers
    (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (stretchLabelComputer selected replacement)

noncomputable def stretchLabel_raw_outputs (selected replacement : ℕ) (raw : Bits)
    (n : ℕ) (g : MixedCode) (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (n,g)) :
    Turing.TM2OutputsInTime (stretchLabelRawComputer selected replacement).tm
      (raw.map (stretchLabelRawComputer selected replacement).inputAlphabet.symm)
      (some ((encoding.encode (g.stretchLabel selected replacement n)).map
        (stretchLabelRawComputer selected replacement).outputAlphabet.symm))
      ((stretchLabelRawComputer selected replacement).time.eval raw.length) := by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding) := ⟨raw,⟨(n,g),hd⟩⟩
  have hv : w.value=(n,g) := BitEncoding.ValidWord.value_eq hd
  have h := (stretchLabelRawComputer selected replacement).outputsFun w
  simpa only [BitEncoding.toFinEncoding, BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw, w, hv] using h

end PlanarHom.Complexity.MixedCode

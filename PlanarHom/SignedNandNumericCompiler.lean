import PlanarHom.PositiveRoutingMachines
import PlanarHom.ListDedupMachines
import PlanarHom.ListIndexMachines
import PlanarHom.NatListSumMachines
import PlanarHom.MixedEvaluationPromises

/-! A fully materialized numeric signed-NAND graph. Only repeated unordered
NAND adjacencies are coalesced; all original Boolean vertices and clause centers
remain, and exactly one marked unary is placed on every fresh center. -/
namespace PlanarHom.SignedNandNumeric
open Complexity ParsimoniousNorOneInThree PairProjectionMachines ArithmeticCircuitPrimitives

abbrev Edge := ℕ × ℕ
abbrev edgeEncoding : BitEncoding Edge := BitEncoding.nat.prod BitEncoding.nat

def normalize (e : Edge) : Edge := if e.2<e.1 then (e.2,e.1) else e

def edgeTest (p : Edge × Edge) : Bool := decide (p.1=p.2)

def clauseEdges (n : ℕ) (p : Clause ℕ × ℕ) : List Edge :=
  let c := p.1
  let z := n+p.2
  [(c.1,c.2.1),(c.2.1,c.2.2),(c.2.2,c.1),(c.1,z),(c.2.1,z),(c.2.2,z)]

def rawEdges (f : NumericFormula) : List Edge := f.2.zipIdx.flatMap (clauseEdges f.1)

def edges (f : NumericFormula) : List Edge := ListDedupMachines.dedup edgeTest ((rawEdges f).map normalize)

def compile (f : NumericFormula) : MixedCode :=
  ⟨f.1+f.2.length,(edges f).map (fun e => (e.1,e.2,0)),
    (List.range f.2.length).map (fun i => (f.1+i,0))⟩

theorem normalized_mem (f : NumericFormula) (e : Edge) (he : e∈edges f) :
    ∃ r∈rawEdges f,normalize r=e :=
  List.mem_map.mp ((ListDedupMachines.dedup_sublist edgeTest _).subset he)

theorem raw_bound (f : NumericFormula) (hf : NumericValid f) (e : Edge) (he : e∈rawEdges f) :
    e.1<f.1+f.2.length ∧ e.2<f.1+f.2.length := by
  obtain ⟨⟨c,j⟩,hc,he⟩ := List.mem_flatMap.mp he
  have hci := hf c (List.fst_mem_of_mem_zipIdx hc)
  have hj : j<f.2.length := by simpa using List.snd_lt_of_mem_zipIdx hc
  simp only [clauseEdges,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega

theorem compile_valid (f : NumericFormula) (hf : NumericValid f) : (compile f).Valid 1 1 := by
  constructor
  · intro e he
    change e∈(edges f).map (fun e => (e.1,e.2,0)) at he
    obtain ⟨q,hq,hqe⟩ := List.mem_map.mp he
    subst e
    obtain ⟨r,hr,hre⟩ := normalized_mem f q hq
    subst q
    have h := raw_bound f hf r hr
    by_cases hs : r.2<r.1 <;> simp [compile,normalize,hs] <;> omega
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
    have h := List.mem_range.mp hi
    change f.1+i<f.1+f.2.length ∧ 0<1
    omega

theorem fp_normalize : FP edgeEncoding edgeEncoding normalize := by
  have ha := fp_fst BitEncoding.nat BitEncoding.nat
  have hb := fp_snd BitEncoding.nat BitEncoding.nat
  exact ((hb.pair ha).comp BinaryArithmetic.fp_comparison).ite (hb.pair ha) (fp_id edgeEncoding)

theorem fp_edgeTest : FP (edgeEncoding.prod edgeEncoding) BitEncoding.bool edgeTest := by
  have hl := fp_fst edgeEncoding edgeEncoding
  have hr := fp_snd edgeEncoding edgeEncoding
  have ha := ((hl.comp (fp_fst _ _)).pair (hr.comp (fp_fst _ _))).comp NatListSumMachines.fp_equal
  have hb := ((hl.comp (fp_snd _ _)).pair (hr.comp (fp_snd _ _))).comp NatListSumMachines.fp_equal
  exact (ha.ite hb (fp_const _ BitEncoding.bool false)).congr (fun p => by
    change (if p.1.1=p.2.1 then decide (p.1.2=p.2.2) else false)=decide (p.1=p.2)
    by_cases h1 : p.1.1=p.2.1 <;> by_cases h2 : p.1.2=p.2.2 <;> simp [Prod.ext_iff,h1,h2])

abbrev clauseInputEncoding : BitEncoding (ℕ × (Clause ℕ × ℕ)) :=
  BitEncoding.nat.prod (clauseEncoding.prod BitEncoding.nat)

theorem fp_clauseEdges : FP clauseInputEncoding edgeEncoding.list (fun p => clauseEdges p.1 p.2) := by
  have hn := fp_fst BitEncoding.nat (clauseEncoding.prod BitEncoding.nat)
  have hp := fp_snd BitEncoding.nat (clauseEncoding.prod BitEncoding.nat)
  have hc := hp.comp (fp_fst clauseEncoding BitEncoding.nat)
  have hi := hp.comp (fp_snd clauseEncoding BitEncoding.nat)
  have hz := (hn.pair hi).comp BinaryArithmetic.fp_addition
  have hx := hc.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hyz := hc.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hy := hyz.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv := hyz.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have h6 := ((hv.pair hz).pair (fp_const clauseInputEncoding edgeEncoding.list [])).comp (ListMutationMachines.fp_cons edgeEncoding)
  have h5 := ((hy.pair hz).pair h6).comp (ListMutationMachines.fp_cons edgeEncoding)
  have h4 := ((hx.pair hz).pair h5).comp (ListMutationMachines.fp_cons edgeEncoding)
  have h3 := ((hv.pair hx).pair h4).comp (ListMutationMachines.fp_cons edgeEncoding)
  have h2 := ((hy.pair hv).pair h3).comp (ListMutationMachines.fp_cons edgeEncoding)
  exact ((hx.pair hy).pair h2).comp (ListMutationMachines.fp_cons edgeEncoding)

theorem fp_rawEdges : FP formulaEncoding edgeEncoding.list rawEdges := by
  have hn := (fp_fst BitEncoding.unaryNat clauseEncoding.list).comp UnaryNatConversionMachine.fp_conversion
  have hc := fp_snd BitEncoding.unaryNat clauseEncoding.list
  have hzip := hc.comp (ListIndexMachines.fp_zipIdx clauseEncoding)
  exact (((hn.pair hzip).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat
    (clauseEncoding.prod BitEncoding.nat) edgeEncoding.list (fun p => clauseEdges p.1 p.2) fp_clauseEdges)).comp
    (ListFlattenMachines.fp_flatten edgeEncoding)).congr (fun _ => rfl)

theorem fp_edges : FP formulaEncoding edgeEncoding.list edges :=
  (fp_rawEdges.comp (ListMapMachines.fp_map edgeEncoding edgeEncoding normalize fp_normalize)).comp
    (ListDedupMachines.fp_dedup edgeEncoding edgeTest fp_edgeTest)

/-- All edges, distinct center indices, unary factors, binary references and
unary vertex headers are emitted by actual finite-control machines. -/
theorem fp_compile : FP formulaEncoding MixedCode.encoding compile := by
  have hn := fp_fst BitEncoding.unaryNat clauseEncoding.list
  have hc := fp_snd BitEncoding.unaryNat clauseEncoding.list
  have hl := hc.comp (ListUnaryLengthMachine.fp_length clauseEncoding)
  have hn' := (hn.pair hl).comp UnaryPolynomialMachines.fp_add
  have he : FP edgeEncoding (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
      (fun e : Edge => (e.1,e.2,0)) :=
    (fp_fst _ _).pair ((fp_snd _ _).pair (fp_const _ BitEncoding.nat 0))
  have hes := fp_edges.comp (ListMapMachines.fp_map edgeEncoding _ _ he)
  have hu : FP edgeEncoding edgeEncoding (fun p : ℕ × ℕ => (p.1+p.2,0)) :=
    BinaryArithmetic.fp_addition.pair (fp_const _ BitEncoding.nat 0)
  have his := hl.comp PositiveBlockProgram.fp_range
  have hus := (((hn.comp UnaryNatConversionMachine.fp_conversion).pair his).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat edgeEncoding _ hu))
  exact (hn'.pair (hes.pair hus)).transportOutput (fun _ => rfl)

end PlanarHom.SignedNandNumeric

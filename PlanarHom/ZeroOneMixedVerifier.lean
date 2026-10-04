import PlanarHom.ZeroOneSharpPMembership
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.RootedHomogeneousSemantics

/-! NEW actual mixed-code validity and verifier machines. The raw graph keeps
every binary occurrence; the one-label, no-unary promise is checked explicitly. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneMixedMembership
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ZeroOneSharpPMembership

theorem fp_underlying : FP MixedCode.encoding GraphCode.encoding MixedCode.underlying := by
  let edgeCode:=BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have he:=(fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).pair
    ((fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst BitEncoding.nat BitEncoding.nat))
  have hes:=MixedCode.fp_edges.comp (ListMapMachines.fp_map edgeCode (BitEncoding.nat.prod BitEncoding.nat) _ he)
  exact (MixedCode.fp_vertices.pair hes).transportOutput (fun _=>rfl)

theorem valid_iff (g:MixedCode) : g.Valid 1 0 ↔
    g.underlying.Valid ∧ (∀e∈g.edges,e.2.2=0) ∧ g.unaries=[] := by
  constructor
  · intro h
    refine ⟨g.underlying_valid h,?_,MixedCode.unaries_nil_of_valid_zero g h⟩
    intro e he
    have hh:=(h.1 e he).2.2
    omega
  · rintro ⟨hg,hl,hu⟩
    constructor
    · intro e he
      have hh:=hg (e.1,e.2.1) (List.mem_map.mpr ⟨e,he,rfl⟩)
      exact ⟨hh.1,hh.2,by rw [hl e he]; decide⟩
    · simp [hu]

theorem fp_valid : FP MixedCode.encoding BitEncoding.bool (fun g=>decide (g.Valid 1 0)) := by
  let edgeCode:=BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hlabel:=(fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_snd BitEncoding.nat BitEncoding.nat)
  have he:=(hlabel.pair (fp_const edgeCode BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hall:=(MixedCode.fp_edges.comp (ListMapMachines.fp_map edgeCode BitEncoding.bool _ he)).comp
    MultiGraph.Kasteleyn.fp_allBool
  have hu:=MixedCode.fp_unaries.comp (ListCodecMachines.fp_length (BitEncoding.nat.prod BitEncoding.nat))
  have hempty:=(hu.pair (fp_const MixedCode.encoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hfirst:=((fp_underlying.comp fp_graphValid).pair hall).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact ((hfirst.pair hempty).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun g=>by
    apply Bool.eq_iff_iff.mpr
    simp [Function.comp_def,List.all_map,List.all_eq_true,valid_iff,and_assoc])

def verifier (q:ℕ) (R:Relation q) (p:Bits×Bits) : Bool :=
  let g:=MixedCode.totalParser.run p.1
  g.1 && decide (g.2.Valid 1 0) && verifyGraph q R g.2.underlying p.2

theorem fp_verifier (q:ℕ) (R:Relation q) :
    FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool (verifier q R) := by
  have hraw:=fp_fst BitEncoding.bits BitEncoding.bits
  have hw:=fp_snd BitEncoding.bits BitEncoding.bits
  have hp:=hraw.comp MixedCode.fp_totalParser
  have hflag:=hp.comp (fp_fst BitEncoding.bool MixedCode.encoding)
  have hg:=hp.comp (fp_snd BitEncoding.bool MixedCode.encoding)
  have hfirst:=(hflag.pair (hg.comp fp_valid)).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hlast:=((hg.comp fp_underlying).pair hw).comp (fp_verifyGraph q R)
  exact (hfirst.pair hlast).comp (fp_bool_gate (fun p=>p.1 && p.2))
end PlanarHom.ZeroOneMixedMembership

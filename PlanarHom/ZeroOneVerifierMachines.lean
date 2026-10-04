import PlanarHom.ZeroOneVerifierPrimitives

/-! NEW actual polynomial-time verifier for a fixed zero-one relation. It
checks endpoint validity, one-hot vertex colors, every edge occurrence, and
unique zero padding, with all list construction and bit lookup charged. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

theorem fp_graphValid : FP GraphCode.encoding BitEncoding.bool (fun g=>decide g.Valid) := by
  let ec:=BitEncoding.nat
  let ee:=BitEncoding.nat.prod BitEncoding.nat
  have hn:=fp_fst ec ee
  have he:=fp_snd ec ee
  have hu:=((he.comp (fp_fst BitEncoding.nat BitEncoding.nat)).pair hn).comp BinaryArithmetic.fp_comparison
  have hv:=((he.comp (fp_snd BitEncoding.nat BitEncoding.nat)).pair hn).comp BinaryArithmetic.fp_comparison
  have hb:=(hu.pair hv).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hnGraph:=GraphCode.fp_vertices.comp UnaryNatConversionMachine.fp_conversion
  exact ((hnGraph.pair GraphCode.fp_edges).comp (fp_allContext ec ee _ hb)).congr
    (fun g=>by apply Bool.eq_iff_iff.mpr; simp [GraphCode.Valid,List.all_eq_true])

theorem fp_padding (q:ℕ) : FP (BitEncoding.unaryNat.prod BitEncoding.bits) BitEncoding.bool
    (fun p=>padding p.1 q p.2) := by
  let ec:=BitEncoding.unaryNat.prod BitEncoding.bits
  have hc:=fp_fst ec BitEncoding.nat
  have hi:=fp_snd ec BitEncoding.nat
  have hn:=hc.comp (fp_fst BitEncoding.unaryNat BitEncoding.bits) |>.comp UnaryNatConversionMachine.fp_conversion
  have hw:=hc.comp (fp_snd BitEncoding.unaryNat BitEncoding.bits)
  have hbound:=(hn.pair (fp_const (ec.prod BitEncoding.nat) BitEncoding.nat q)).comp BinaryArithmetic.fp_multiplication
  have hlt:=(hi.pair hbound).comp BinaryArithmetic.fp_comparison
  have hbit:=(hw.pair hi).comp fp_getBit
  have hbody:=(hlt.pair hbit).comp (fp_bool_gate (fun p=>p.1 || !p.2))
  have hlen:FP BitEncoding.bits BitEncoding.unaryNat (fun w:Bits=>w.length) := ⟨InputLengthMachine.computer BitEncoding.bits⟩
  have his:=(fp_snd BitEncoding.unaryNat BitEncoding.bits).comp hlen |>.comp fp_range
  exact (((fp_id ec).pair his).comp (fp_allContext ec BitEncoding.nat _ hbody)).congr (fun p=>by
    change (List.range p.2.length).all (fun k=>decide (k<p.1*q) || !(getBit p.2 k))=padding p.1 q p.2
    unfold padding
    congr 1
    funext k
    by_cases hk:k<p.1*q <;> simp [hk])

theorem fp_verifyGraph (q:ℕ) (R:Relation q) :
    FP (GraphCode.encoding.prod BitEncoding.bits) BitEncoding.bool (fun p=>verifyGraph q R p.1 p.2) := by
  have hg:=fp_fst GraphCode.encoding BitEncoding.bits
  have hw:=fp_snd GraphCode.encoding BitEncoding.bits
  have hvalid:=hg.comp fp_graphValid
  have hn:=hg.comp GraphCode.fp_vertices
  have hvs:=hn.comp fp_range
  have hvertices:=(hw.pair hvs).comp (fp_allContext BitEncoding.bits BitEncoding.nat _ (fp_vertexCheck q))
  have he:=hg.comp GraphCode.fp_edges
  have hedges:=(hw.pair he).comp (fp_allContext BitEncoding.bits (BitEncoding.nat.prod BitEncoding.nat) _ (fp_edgeCheck q R))
  have hpad:=(hn.pair hw).comp (fp_padding q)
  have hfirst:=(hvalid.pair hvertices).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hsecond:=(hfirst.pair hedges).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact (hsecond.pair hpad).comp (fp_bool_gate (fun p=>p.1 && p.2))
end PlanarHom.ZeroOneSharpPMembership

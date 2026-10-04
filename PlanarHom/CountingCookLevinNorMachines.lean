import PlanarHom.CountingCookLevinNorCircuit
import PlanarHom.FixedVectorMachines

/-! Actual bit-level emission of each fixed local Boolean expression template. -/
namespace PlanarHom.CountingCookLevin
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def templateInputEncoding (d : ℕ) : BitEncoding (ℕ × (Fin d → ℕ)) :=
  BitEncoding.nat.prod (BitEncoding.nat.vector d)

theorem fp_template_offset (d k : ℕ) : FP (templateInputEncoding d) (templateInputEncoding d)
    (fun p => (p.1+k,p.2)) := by
  have hn := fp_fst BitEncoding.nat (BitEncoding.nat.vector d)
  have hv := fp_snd BitEncoding.nat (BitEncoding.nat.vector d)
  exact ((hn.pair (fp_const (templateInputEncoding d) BitEncoding.nat k)).comp
    BinaryArithmetic.fp_addition).pair hv

theorem Expr.fp_output {d : ℕ} (e : Expr (Fin d)) :
    FP (templateInputEncoding d) BitEncoding.nat (fun p => e.output p.1 p.2) := by
  cases e with
  | var v =>
    exact (fp_snd BitEncoding.nat (BitEncoding.nat.vector d)).comp
      (FixedVectorMachines.fp_coordinate BitEncoding.nat d v)
  | nor a b =>
    exact ((fp_fst BitEncoding.nat (BitEncoding.nat.vector d)).pair
      (fp_const (templateInputEncoding d) BitEncoding.nat (4*(a.gates+b.gates)))).comp
        BinaryArithmetic.fp_addition

theorem Expr.fp_emit {d : ℕ} (e : Expr (Fin d)) :
    FP (templateInputEncoding d) (BitEncoding.nat.prod BitEncoding.nat).list
      (fun p => e.emit p.1 p.2) := by
  let eg := BitEncoding.nat.prod BitEncoding.nat
  induction e with
  | var v => exact fp_const (templateInputEncoding d) eg.list []
  | nor a b ha hb =>
    have hshift := fp_template_offset d (4*a.gates)
    have hleft := ha
    have hright := hshift.comp hb
    have hp := a.fp_output.pair (hshift.comp b.fp_output)
    have hlast := (hp.pair (fp_const (templateInputEncoding d) eg.list [])).comp
      (ListMutationMachines.fp_cons eg)
    have hab := (hleft.pair hright).comp (ListMutationMachines.fp_append eg)
    exact (hab.pair hlast).comp (ListMutationMachines.fp_append eg)

/-- One genuine machine emits both the shared-register gate list and its output
index. Template size is fixed source-machine data, not an oracle operation. -/
theorem Expr.fp_compile {d : ℕ} (e : Expr (Fin d)) :
    FP (templateInputEncoding d) ((BitEncoding.nat.prod BitEncoding.nat).list.prod BitEncoding.nat)
      (fun p => (e.emit p.1 p.2,e.output p.1 p.2)) := e.fp_emit.pair e.fp_output

end PlanarHom.CountingCookLevin

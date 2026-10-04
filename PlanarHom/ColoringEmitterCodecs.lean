import PlanarHom.ColoringEmitterProgram
import PlanarHom.NatListSumMachines

/-! NEW honest binary/list codecs and total lookup machines for the emitter. -/
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives

def edgeEncoding : BitEncoding EdgeCode := referenceEncoding
def addressEncoding : BitEncoding Address := referenceEncoding

def statePartsEncoding : BitEncoding (ℕ × (List ℕ × (ℕ × List EdgeCode))) :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.list.prod (BitEncoding.unaryNat.prod edgeEncoding.list))

def stateEncoding : BitEncoding State := statePartsEncoding.retract
  (fun s=>(s.sourceBase,s.dictionary,s.vertices,s.edges))
  (fun p=>⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩) (by intro s; cases s; rfl)

theorem fp_parts : FP stateEncoding statePartsEncoding
    (fun s=>(s.sourceBase,s.dictionary,s.vertices,s.edges)) := fp_code_view _ _ _ (fun _=>rfl)
theorem fp_build : FP statePartsEncoding stateEncoding
    (fun p=>⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩) := fp_code_view _ _ _ (fun _=>rfl)
theorem fp_sourceBase : FP stateEncoding BitEncoding.unaryNat State.sourceBase :=
  fp_parts.comp (fp_fst _ _)
theorem fp_dictionary : FP stateEncoding BitEncoding.nat.list State.dictionary :=
  fp_parts.comp ((fp_snd _ _).comp (fp_fst _ _))
theorem fp_vertices : FP stateEncoding BitEncoding.unaryNat State.vertices :=
  fp_parts.comp ((fp_snd _ _).comp ((fp_snd _ _).comp (fp_fst _ _)))
theorem fp_edges : FP stateEncoding edgeEncoding.list State.edges :=
  fp_parts.comp ((fp_snd _ _).comp ((fp_snd _ _).comp (fp_snd _ _)))

/-- Any one of the four fixed macro tables is retrieved by actual finite control. -/
theorem fp_kindFunction {A : Type} (ea : BitEncoding A) (f : Kind→A) : FP kindEncoding ea f := by
  have hhi:=fp_kindCode.comp (fp_fst BitEncoding.bool BitEncoding.bool)
  have hlo:=fp_kindCode.comp (fp_snd BitEncoding.bool BitEncoding.bool)
  have hfalse:=(hlo.pair ((fp_const kindEncoding ea (f .cross)).pair (fp_const kindEncoding ea (f .wire)))).comp (ConditionalMachines.fp_select ea)
  have htrue:=(hlo.pair ((fp_const kindEncoding ea (f .test)).pair (fp_const kindEncoding ea (f .fan)))).comp (ConditionalMachines.fp_select ea)
  exact ((hhi.pair (htrue.pair hfalse)).comp (ConditionalMachines.fp_select ea)).congr (fun k=>by cases k <;> rfl)

/-- Total binary-index lookup, with the exact explicit fallback. -/
theorem fp_getD {A : Type} (ea : BitEncoding A) (d : A) :
    FP (ea.list.prod BitEncoding.nat) ea (fun p=>p.1[p.2]?.getD d) := by
  have hl:=fp_fst ea.list BitEncoding.nat
  have hi:=fp_snd ea.list BitEncoding.nat
  have h:=((hi.pair hl).comp (ListDropMachines.fp_drop ea d)).comp
    (ListDecompositionMachines.fp_headD ea d)
  exact h.congr (fun p=>by change (p.1.drop p.2).headD d=p.1[p.2]?.getD d; rw [List.headD_eq_head?_getD,List.head?_drop])

def contextEncoding : BitEncoding (Instruction × (List ℕ × ℕ)) :=
  instructionEncoding.prod (BitEncoding.nat.list.prod BitEncoding.nat)

end PlanarHom.ColoringEmitter

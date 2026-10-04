import PlanarHom.RawFramesParserMachines
import PlanarHom.NatCanonicalizationMachine
import PlanarHom.MachineCodeTransport

/-! NEW compositional total decoders with actual FP witnesses. Failure is a
Boolean flag with an explicit total payload; correctness covers every raw word. -/
noncomputable section
namespace PlanarHom.Complexity.BitEncoding
open PairProjectionMachines ArithmeticCircuitPrimitives

structure TotalParser {A:Type} (e:BitEncoding A) where
  run:Bits→Bool×A
  fp:FP bits (bool.prod e) run
  correct:∀raw,e.decode raw=if (run raw).1 then some (run raw).2 else none

namespace TotalParser
variable {A B:Type} {ea:BitEncoding A} {eb:BitEncoding B}

def nat : TotalParser BitEncoding.nat where
  run raw:=(true,Computability.decodeNat raw)
  fp:=(fp_const bits bool true).pair ⟨NatCanonicalizationMachine.decodeComputer⟩
  correct _:=rfl

def unaryNat : TotalParser BitEncoding.unaryNat where
  run raw:=(true,raw.length)
  fp:=(fp_const bits bool true).pair ⟨InputLengthMachine.computer bits⟩
  correct _:=rfl

def rawBits : TotalParser bits where
  run raw:=(true,raw)
  fp:=(fp_const bits bool true).pair (fp_id bits)
  correct _:=rfl

def pairRun (pa:TotalParser ea) (pb:TotalParser eb) (raw:Bits) : Bool×(A×B) :=
  let f:=RawFrameParser.parse raw
  let a:=pa.run f.2.1
  let b:=pb.run f.2.2
  (f.1 && a.1 && b.1,a.2,b.2)

theorem fp_pairRun (pa:TotalParser ea) (pb:TotalParser eb) :
    FP bits (bool.prod (ea.prod eb)) (pairRun pa pb) := by
  have hf:=RawFrameParser.fp_parse
  have hflag:=hf.comp (fp_fst bool (bits.prod bits))
  have hp:=hf.comp (fp_snd bool (bits.prod bits))
  have ha:=(hp.comp (fp_fst bits bits)).comp pa.fp
  have hb:=(hp.comp (fp_snd bits bits)).comp pb.fp
  have hok:=((hflag.pair (ha.comp (fp_fst bool ea))).comp (fp_bool_gate (fun p=>p.1 && p.2))).pair
    (hb.comp (fp_fst bool eb)) |>.comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact hok.pair ((ha.comp (fp_snd bool ea)).pair (hb.comp (fp_snd bool eb)))

theorem pairRun_correct (pa:TotalParser ea) (pb:TotalParser eb) (raw:Bits) :
    (ea.prod eb).decode raw=if (pairRun pa pb raw).1 then some (pairRun pa pb raw).2 else none := by
  simp only [BitEncoding.prod,RawFrameParser.parse_spec]
  cases hf:(RawFrameParser.parse raw).1 <;>
    cases ha:(pa.run (RawFrameParser.parse raw).2.1).1 <;>
    cases hb:(pb.run (RawFrameParser.parse raw).2.2).1 <;>
    simp [pairRun,hf,ha,hb,pa.correct,pb.correct]

def prod (pa:TotalParser ea) (pb:TotalParser eb) : TotalParser (ea.prod eb) :=
  ⟨pairRun pa pb,fp_pairRun pa pb,pairRun_correct pa pb⟩

def retract {C:Type} (pa:TotalParser ea) (f:C→A) (g:A→C) (hgf:∀c,g (f c)=c)
    (hfg:∀a,f (g a)=a) : TotalParser (ea.retract f g hgf) where
  run raw:=((pa.run raw).1,g (pa.run raw).2)
  fp:=pa.fp.transportOutput (by intro raw; simp only [BitEncoding.prod,BitEncoding.retract,hfg])
  correct raw:=by
    simp only [BitEncoding.retract,pa.correct]
    cases h:(pa.run raw).1 <;> simp [h]
end TotalParser
end PlanarHom.Complexity.BitEncoding

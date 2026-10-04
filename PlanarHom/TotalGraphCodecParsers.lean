import PlanarHom.TotalListCodecParser

/-! NEW total polynomial-time parsers for the unchanged graph and mixed graph
codecs, including every noncanonical successful word and explicit failure. -/
noncomputable section
namespace PlanarHom.Complexity
open BitEncoding

namespace GraphCode
 def totalParser : TotalParser encoding :=
   ((TotalParser.unaryNat).prod ((TotalParser.nat.prod TotalParser.nat).list)).retract
     (fun g:GraphCode=>(g.vertices,g.edges)) (fun p=>⟨p.1,p.2⟩)
     (by intro g; cases g; rfl) (by intro p; cases p; rfl)
 theorem totalParser_correct (raw:Bits) : encoding.decode raw=
     if (totalParser.run raw).1 then some (totalParser.run raw).2 else none := totalParser.correct raw
 theorem fp_totalParser : FP BitEncoding.bits (BitEncoding.bool.prod encoding) totalParser.run := totalParser.fp
end GraphCode
namespace MixedCode
 def totalParser : TotalParser encoding :=
   (TotalParser.unaryNat.prod
     ((TotalParser.nat.prod (TotalParser.nat.prod TotalParser.nat)).list.prod
       (TotalParser.nat.prod TotalParser.nat).list)).retract
     (fun g:MixedCode=>(g.vertices,g.edges,g.unaries)) (fun p=>⟨p.1,p.2.1,p.2.2⟩)
     (by intro g; cases g; rfl) (by intro p; rcases p with ⟨n,e,u⟩; rfl)
 theorem totalParser_correct (raw:Bits) : encoding.decode raw=
     if (totalParser.run raw).1 then some (totalParser.run raw).2 else none := totalParser.correct raw
 theorem fp_totalParser : FP BitEncoding.bits (BitEncoding.bool.prod encoding) totalParser.run := totalParser.fp
end MixedCode
end PlanarHom.Complexity

import PlanarHom.ColoringEmitterRowProgram
import PlanarHom.ListFlattenMachines
import PlanarHom.MixedUnaryParallelMachines

/-! NEW actual polynomial-time row materialization from the formula alone.
All prefix states are computed by the verified emitter; no inverse or row oracle
appears in the runtime input. The four finite row tables are fixed constants. -/
namespace PlanarHom.ColoringEmitterRows
open Complexity PositiveBlockProgram ParsimoniousNorOneInThree ColoringEmitter
open PairProjectionMachines ArithmeticCircuitPrimitives
abbrev cellCode := stateEncoding.prod (instructionEncoding.prod BitEncoding.nat)
abbrev programCode := BitEncoding.unaryNat.prod (instructionEncoding.list.prod BitEncoding.nat)

 theorem fp_cellRow (table : RowTable) : FP cellCode dartCode.list
     (fun p=>cellRow table p.1 p.2.1 p.2.2) := by
   let ec:=cellCode.prod BitEncoding.nat
   have hc:=fp_fst cellCode BitEncoding.nat
   have hw:=fp_snd cellCode BitEncoding.nat
   have hs:=hc.comp (fp_fst stateEncoding (instructionEncoding.prod BitEncoding.nat))
   have hov:=hc.comp (fp_snd stateEncoding (instructionEncoding.prod BitEncoding.nat))
   have ho:=hov.comp (fp_fst instructionEncoding BitEncoding.nat)
   have hv:=hov.comp (fp_snd instructionEncoding BitEncoding.nat)
   have hk:=ho.comp (fp_fst kindEncoding referenceEncoding)
   have hctx:=ho.pair ((hs.comp fp_dictionary).pair ((hs.comp ColoringEmitter.fp_vertices).comp UnaryNatConversionMachine.fp_conversion))
   have heq:=((hctx.pair hw).comp fp_localVertex).pair hv |>.comp NatListSumMachines.fp_equal
   have htab:=(hk.comp (fp_kindFunction rowsCode table)).pair hw |>.comp (fp_getD dartCode.list [])
   have hoff:=(hs.comp fp_edges).comp (ListUnaryLengthMachine.fp_length edgeEncoding) |>.comp UnaryNatConversionMachine.fp_conversion
   have hn:=fp_fst BitEncoding.nat dartCode
   have hd:=fp_snd BitEncoding.nat dartCode
   have hlift:=((hn.pair (hd.comp (fp_fst BitEncoding.nat BitEncoding.bool))).comp BinaryArithmetic.fp_addition).pair
     (hd.comp (fp_snd BitEncoding.nat BitEncoding.bool))
   have hm:=(hoff.pair htab).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat dartCode dartCode _ hlift)
   have hbody:=(heq.pair (hm.pair (fp_const ec dartCode.list []))).comp (ConditionalMachines.fp_select dartCode.list)
   have hkind:=(fp_snd stateEncoding (instructionEncoding.prod BitEncoding.nat)).comp
     (fp_fst instructionEncoding BitEncoding.nat) |>.comp (fp_fst kindEncoding referenceEncoding)
   have hws:=hkind.comp (fp_kindFunction BitEncoding.nat.list (fun k=>List.range (Macro.vertexCount k)))
   have hall:=((fp_id cellCode).pair hws).comp
     (ListContextMachines.fp_mapWithContext cellCode BitEncoding.nat dartCode.list _ hbody)
   exact (hall.comp (ListFlattenMachines.fp_flatten dartCode)).congr (fun p=>by
     simp only [Function.comp_apply,cellRow,List.flatMap,List.map_map]
     congr 1
     apply List.map_congr_left
     intro w _
     simp only [id_eq,decide_eq_true_eq]
     )

 theorem fp_programRow (table : RowTable) : FP programCode dartCode.list
     (fun p=>programRow table p.1 p.2.1 p.2.2) := by
   let ec:=programCode.prod BitEncoding.nat
   have hp:=fp_fst programCode BitEncoding.nat
   have hi:=fp_snd programCode BitEncoding.nat
   have hn:=hp.comp (fp_fst BitEncoding.unaryNat (instructionEncoding.list.prod BitEncoding.nat))
   have hov:=hp.comp (fp_snd BitEncoding.unaryNat (instructionEncoding.list.prod BitEncoding.nat))
   have hops:=hov.comp (fp_fst instructionEncoding.list BitEncoding.nat)
   have hv:=hov.comp (fp_snd instructionEncoding.list BitEncoding.nat)
   have htake:=(hi.pair hops).comp (PositiveBlockProgram.fp_take instructionEncoding (.wire,0,0,0))
   have hseed:FP ec seedEncoding (fun p=>(p.1.1,p.1.2.1.take p.2)) :=
     ((hn.comp fp_initial).pair htake).transportOutput (fun _=>rfl)
   have hs:=hseed.comp fp_run
   have hop:=(hops.pair hi).comp (fp_getD instructionEncoding (.wire,0,0,0))
   have hbody:=(hs.pair (hop.pair hv)).comp (fp_cellRow table)
   have hos:=(fp_snd BitEncoding.unaryNat (instructionEncoding.list.prod BitEncoding.nat)).comp
     (fp_fst instructionEncoding.list BitEncoding.nat)
   have hindices:=(hos.comp (ListUnaryLengthMachine.fp_length instructionEncoding)).comp fp_range |>.comp
     (ListReverseMachines.fp_reverse BitEncoding.nat)
   have hall:=((fp_id programCode).pair hindices).comp
     (ListContextMachines.fp_mapWithContext programCode BitEncoding.nat dartCode.list _ hbody)
   exact (hall.comp (ListFlattenMachines.fp_flatten dartCode)).congr (fun _=>rfl)

 theorem fp_rows (table : RowTable) : FP formulaEncoding rowsCode (rows table) := by
   have hf:=fp_fst formulaEncoding BitEncoding.nat
   have hv:=fp_snd formulaEncoding BitEncoding.nat
   have hn:=hf.comp (fp_fst BitEncoding.unaryNat clauseEncoding.list)
   have hops:=hf.comp PositiveBlockProgram.fp_program
   have hbody:=(hn.pair (hops.pair hv)).comp (fp_programRow table)
   have hverts:=ColoringEmitter.fp_compile.comp MixedCode.fp_vertices |>.comp fp_range
   exact ((fp_id formulaEncoding).pair hverts).comp
     (ListContextMachines.fp_mapWithContext formulaEncoding BitEncoding.nat dartCode.list _ hbody)
end PlanarHom.ColoringEmitterRows

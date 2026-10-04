import PlanarHom.PlanarityDepthFirstSearchNeighbours

/-! NEW reconstruction. Actual encoded FP for one DFS transition, initial root
stack, and the unary-charged polynomial execution clock. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 theorem fp_step : FP (MixedCode.encoding.prod stateCode) stateCode (fun p=>step p.1 p.2) := by
  let ei := MixedCode.encoding.prod stateCode
  have hg := fp_fst MixedCode.encoding stateCode
  have hs := fp_snd MixedCode.encoding stateCode
  have hw := hs.comp fp_work
  have ha := hs.comp fp_active
  have hd := hs.comp fp_discovered
  have hf := hs.comp fp_finished
  have ht := hw.comp (ListDecompositionMachines.fp_headD taskCode (exitTask 0))
  have hr := hw.comp (ListDecompositionMachines.fp_tail taskCode (exitTask 0))
  have hv := ht.comp fp_vertex
  have he := ht.comp fp_edge
  have hpath := (hv.pair ha).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hchildren := (hg.pair (hv.pair hpath)).comp fp_childTasks
  have hexit := hv.comp fp_exitTask
  have hreturn := (hexit.pair hr).comp (ListMutationMachines.fp_cons taskCode)
  have hwork' := (hchildren.pair hreturn).comp (ListMutationMachines.fp_append taskCode)
  have hrecord := fp_mkDiscovery ei _ _ _ hv he ha
  have hrecords := (hrecord.pair hd).comp (ListMutationMachines.fp_cons discoveryCode)
  have hnew := fp_mkState ei _ _ _ _ hwork' hpath hrecords hf
  have hskip := fp_mkState ei _ _ _ _ hr ha hd hf
  have hpop := ha.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  have hfinish := (hv.pair hf).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hclose := fp_mkState ei _ _ _ _ hr hpop hd hfinish
  have hn := (hg.comp MixedCode.fp_vertices).comp UnaryNatConversionMachine.fp_conversion
  have hvalid := (hv.pair hn).comp BinaryArithmetic.fp_comparison
  have hseen := hs.comp fp_seen
  have hmem := (hv.pair hseen).comp GraphComponentMachines.fp_mem
  have hnot := hmem.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hfresh := (hvalid.pair hnot).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hfresh' : FP ei BitEncoding.bool
      (fun p=>decide ((p.2.work.headD (exitTask 0)).vertex<p.1.vertices ∧
        (p.2.work.headD (exitTask 0)).vertex∉seen p.2)) := hfresh.congr (fun _=>by simp)
  have hopen := ht.comp fp_enter
  have hopen' : FP ei BitEncoding.bool (fun p=>decide ((p.2.work.headD (exitTask 0)).enter=true)) :=
    hopen.congr (fun _=>by simp)
  have hnonempty := hopen'.ite (hfresh'.ite hnew hskip) hclose
  have hz := (hw.comp (ListCodecMachines.fp_length taskCode)).comp RationalCircuits.fp_nat_isZero
  have hz' : FP ei BitEncoding.bool (fun p=>decide (p.2.work=[])) := hz.congr (fun _=>by simp)
  exact (hz'.ite hs hnonempty).congr (fun p=>by
    cases h : p.2.work <;> simp [step,h])

 theorem fp_initial : FP MixedCode.encoding stateCode initial := by
  have hm := (MixedCode.fp_edges).comp (ListCodecMachines.fp_length edgeCode)
  have hr := MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_range
  have he := fp_fst BitEncoding.nat BitEncoding.nat
  have hv := fp_snd BitEncoding.nat BitEncoding.nat
  have ht := fp_mkTask (BitEncoding.nat.prod BitEncoding.nat) _ _ _ _
    (fp_const _ _ true) hv he (fp_const _ _ [])
  have hwork := (hm.pair hr).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat taskCode _ ht)
  exact fp_mkState MixedCode.encoding _ _ _ _ hwork (fp_const _ _ [])
    (fp_const _ _ []) (fp_const _ _ [])

 theorem fp_fuel : FP MixedCode.encoding BitEncoding.unaryNat fuel := by
  have hn := MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_succ
  have hm := MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length edgeCode)
  have htwice := (hm.pair hm).comp UnaryArithmeticMachines.fp_add
  have hthree := (htwice.pair (fp_const MixedCode.encoding BitEncoding.unaryNat 3)).comp UnaryArithmeticMachines.fp_add
  exact ((hn.pair hthree).comp UnaryArithmeticMachines.fp_mul).congr (fun g=>by simp [fuel,Nat.two_mul])

end PlanarHom.PlanarityDepthFirstSearch

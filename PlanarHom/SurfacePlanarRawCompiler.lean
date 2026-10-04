import PlanarHom.SurfacePlanarCompilerCorrectness
import PlanarHom.TotalGraphCodecParsers

/-! NEW raw-word source reduction. It parses the unchanged original MixedCode
codec in polynomial time, retaining every successfully decoded noncanonical
word, and emits the actual finite supplied-embedding format. -/
namespace PlanarHom.SurfacePlanarCompiler
open Complexity SurfaceRawEmbedding

 def rawCompile (ambient:ℕ) (raw:Bits) : Bits :=
  inputCode.encode (compile ambient (MixedCode.totalParser.run raw).2)

 theorem fp_rawCompile (ambient:ℕ) : FP BitEncoding.bits BitEncoding.bits (rawCompile ambient) := by
  have hp:=MixedCode.fp_totalParser.comp (PairProjectionMachines.fp_snd BitEncoding.bool MixedCode.encoding)
  have hc:=hp.comp (fp_compile ambient)
  have he:FP inputCode BitEncoding.bits inputCode.encode:=fp_code_view _ _ _ (fun _=>rfl)
  exact hc.comp he

 theorem parsed_eq {raw:Bits} {g:MixedCode} (hd:MixedCode.encoding.decode raw=some g) :
    (MixedCode.totalParser.run raw).2=g := by
  rw [MixedCode.totalParser_correct] at hd
  split at hd
  · exact Option.some.inj hd
  · cases hd

 theorem rawCompile_decode (ambient:ℕ) {raw:Bits} {g:MixedCode}
    (hd:MixedCode.encoding.decode raw=some g) :
    inputCode.decode (rawCompile ambient raw)=some (compile ambient g) := by
  simp only [rawCompile,parsed_eq hd,inputCode.decode_encode]

 theorem rawCompile_valid (ambient:ℕ) {bt ut:ℕ} {raw:Bits} {g:MixedCode}
    (hd:MixedCode.encoding.decode raw=some g) (hp:g.PlanarValid bt ut) :
    ∃p:Input,inputCode.decode (rawCompile ambient raw)=some p ∧ Input.Valid bt ut ambient p :=
  ⟨compile ambient g,rawCompile_decode ambient hd,compile_valid ambient g hp⟩

 theorem rawCompile_original_graph (ambient:ℕ) {raw:Bits} {g:MixedCode}
    (hd:MixedCode.encoding.decode raw=some g) :
    (compile ambient (MixedCode.totalParser.run raw).2).1=g := parsed_eq hd

end PlanarHom.SurfacePlanarCompiler

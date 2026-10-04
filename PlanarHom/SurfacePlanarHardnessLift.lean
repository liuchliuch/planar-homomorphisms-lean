import PlanarHom.SurfacePlanarRawCompiler
import PlanarHom.SurfaceEvaluationProblem
import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.RawPartitionOutputBounds
import PlanarHom.PromisedSharpPHardness

/-! NEW: the actual planar embedding compiler lifts every ordinary planar
counting-hardness reduction to the supplied orientable-surface input at any
fixed ambient genus. Values and fixed output fields are unchanged. -/
noncomputable section
open Classical
namespace PlanarHom.SurfacePlanarHardness
open Complexity PairProjectionMachines MachineComposition SurfaceRawEmbedding
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

theorem output_bound (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) :
    ∃ p : Polynomial ℕ, ∀ raw, (evaluationProblem ambient basis M U w).valid raw →
      ((evaluationProblem ambient basis M U w).value raw).length ≤ p.eval raw.length := by
  obtain ⟨p,hp⟩ := PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound basis M U w
  let q := outputLengthPolynomial normalizer
  refine ⟨p.comp q,?_⟩
  intro raw hraw
  obtain ⟨a,hd,ha⟩ := hraw
  let v : BitEncoding.ValidWord inputCode := ⟨raw,⟨a,hd⟩⟩
  have hv : v.value = a := BitEncoding.ValidWord.value_eq hd
  have hsize := encoded_output_length_le normalizer v
  change (inputCode.encode v.value).length ≤ q.eval raw.length at hsize
  rw [hv] at hsize
  have hgsize : (MixedCode.encoding.encode a.1).length ≤ (inputCode.encode a).length := by
    simp only [inputCode,BitEncoding.prod_length]
    omega
  have hval := hp (MixedCode.encoding.encode a.1) a.1 (Input.graph_valid ha) (MixedCode.encoding.decode_encode a.1)
  change (evaluationValue basis M U w raw).length ≤ _
  rw [evaluationValue_decode basis M U w raw a hd (Input.graph_valid ha)]
  exact hval.trans (by simpa only [Polynomial.eval_comp] using
    natPolynomial_monotone p (hgsize.trans hsize))

theorem value_rawCompile (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (raw : Bits) (h : (MixedCode.evaluationProblem basis M U w).valid raw) :
    (evaluationProblem ambient basis M U w).value (SurfacePlanarCompiler.rawCompile ambient raw) =
      (MixedCode.evaluationProblem basis M U w).value raw := by
  obtain ⟨g,hd,hg⟩ := h
  change evaluationValue basis M U w _ = MixedCode.evaluationValue basis M U w raw
  rw [evaluationValue_decode basis M U w _ (SurfacePlanarCompiler.compile ambient g)
    (SurfacePlanarCompiler.rawCompile_decode ambient hd) hg.1]
  rw [SurfacePlanarCompiler.compile_value, MixedCode.evaluationValue_decode basis M U w raw g hd hg.1]

def reduction (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) :
    PromisePolyTimeTuringReduction (MixedCode.evaluationProblem basis M U w)
      (evaluationProblem ambient basis M U w) := by
  let p := Classical.choose (output_bound ambient basis M U w)
  have hp := Classical.choose_spec (output_bound ambient basis M U w)
  let target := MixedCode.evaluationProblem basis M U w
  let source := evaluationProblem ambient basis M U w
  have hq : FP BitEncoding.bits BitEncoding.bits.list
      (fun raw => [SurfacePlanarCompiler.rawCompile ambient raw]) :=
    ((SurfacePlanarCompiler.fp_rawCompile ambient).pair (fp_const BitEncoding.bits BitEncoding.bits.list [])).comp
      (ListMutationMachines.fp_cons BitEncoding.bits)
  have hpre := (fp_const BitEncoding.bits BitEncoding.bits []).pair hq
  have hpost := (fp_snd BitEncoding.bits BitEncoding.bits.list).comp
    (ListDecompositionMachines.fp_headD BitEncoding.bits [])
  apply nonadaptiveReduction BitEncoding.bits BitEncoding.bits BitEncoding.bits BitEncoding.bits BitEncoding.bits
    target source (fun raw => ([],[SurfacePlanarCompiler.rawCompile ambient raw])) source.value
    (fun p => p.2.headD []) (Classical.choice hpre) (Classical.choice hpost)
    (fun raw _ => raw) (fun _ _ => rfl) _ _ _ p hp
  · intro raw h query hquery
    have he : query = SurfacePlanarCompiler.rawCompile ambient raw := List.mem_singleton.mp hquery
    subst query
    obtain ⟨g,hd,hg⟩ := h
    exact SurfacePlanarCompiler.rawCompile_valid ambient hd hg
  · intro query _
    rfl
  · intro raw h
    change ([source.value (SurfacePlanarCompiler.rawCompile ambient raw)]).headD [] = target.value raw
    exact value_rawCompile ambient basis M U w raw h

theorem promisedSharpPHard (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (h : PromisedSharpPHard (MixedCode.evaluationProblem basis M U w)) :
    PromisedSharpPHard (evaluationProblem ambient basis M U w) :=
  h.trans (reduction ambient basis M U w)

end PlanarHom.SurfacePlanarHardness

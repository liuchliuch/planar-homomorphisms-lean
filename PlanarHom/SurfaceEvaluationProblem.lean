import PlanarHom.SurfaceInputNormalization
import PlanarHom.MixedEvaluationPromises

/-! NEW exact supplied-surface evaluation promise on all successful raw
encodings, using the original graph's value and fixed-field output codec. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRawEmbedding
open Complexity
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

theorem Input.graph_valid {p : Input} {ambient : ℕ} (h : p.Valid b u ambient) : p.1.Valid b u := by
  obtain ⟨hg,R,hr,hc⟩ := h
  exact hg

def evaluationValue (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) (raw : Bits) : Bits :=
  match inputCode.decode raw with
  | none => []
  | some p => MixedCode.evaluationValue basis M U w (MixedCode.encoding.encode p.1)

def evaluationProblem (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) : PromiseProblem :=
  ⟨(fun raw => ∃p,inputCode.decode raw=some p ∧ p.Valid b u ambient),evaluationValue basis M U w⟩

theorem evaluationValue_decode (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (raw : Bits) (p : Input) (hd : inputCode.decode raw=some p) (hg : p.1.Valid b u) :
    evaluationValue basis M U w raw=(numberFieldEncoding basis).encode (p.1.evaluate hg M U w) := by
  simp only [evaluationValue,hd,MixedCode.evaluationValue_encode basis M U w p.1 hg]

private def rawView (ambient : ℕ)
    (raw : {raw:Bits // ∃p,inputCode.decode raw=some p ∧ p.Valid b u ambient}) :
    BitEncoding.ValidWord inputCode := ⟨raw.val,by obtain ⟨p,hd,hp⟩ := raw.property;exact ⟨p,hd⟩⟩

private theorem rawView_valid (ambient : ℕ)
    (raw : {raw:Bits // ∃p,inputCode.decode raw=some p ∧ p.Valid b u ambient}) :
    (rawView ambient raw).value.Valid b u ambient := by
  obtain ⟨p,hd,hp⟩ := raw.property
  have he : (rawView ambient raw).value=p := BitEncoding.ValidWord.value_eq hd
  simpa only [he] using hp

theorem evaluation_inFP_of (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (h : FP (inputCode.restrict (Input.Valid b u ambient)) (numberFieldEncoding basis)
      (fun p : {p:Input // p.Valid b u ambient} => p.val.1.evaluate (Input.graph_valid p.property) M U w)) :
    (evaluationProblem ambient basis M U w).InFP := by
  let ei := BitEncoding.bits.restrict (evaluationProblem ambient basis M U w).valid
  let decoded : {raw:Bits // (evaluationProblem ambient basis M U w).valid raw} →
      {p:Input // p.Valid b u ambient} := fun raw => ⟨(rawView ambient raw).value,rawView_valid ambient raw⟩
  have hv : FP ei (BitEncoding.ValidWord.encoding inputCode) (rawView (b:=b) (u:=u) ambient) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hn : FP ei (inputCode.restrict (Input.Valid b u ambient)) decoded :=
    (hv.comp ⟨normalizer⟩).transportOutput (fun _ => rfl)
  apply (hn.comp h).transportOutput
  intro raw
  exact (evaluationValue_decode basis M U w raw.val (decoded raw).val
    (BitEncoding.ValidWord.decode_raw (rawView ambient raw)) (Input.graph_valid (decoded raw).property)).symm

end PlanarHom.SurfaceRawEmbedding

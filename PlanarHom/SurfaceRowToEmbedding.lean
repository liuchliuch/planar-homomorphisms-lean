import PlanarHom.SurfaceRowEvaluation
import PlanarHom.SurfaceEvaluationProblem
import PlanarHom.SurfaceGlobalHomologyBound

/-! NEW public raw-input join: the actual complementary-region tables prove
the internal dimension promise, then the supplied-row program evaluates the
unchanged original graph. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRowEvaluation
open Complexity SurfaceRawEmbedding
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

theorem graphRows_valid (ambient : ℕ) {p : SurfaceRawEmbedding.Input}
    (hp : p.Valid b u ambient) : Valid b u ambient (SurfaceRawEmbedding.graphRows p) := by
  obtain ⟨hg,R,hr,hc⟩ := hp
  exact ⟨hg,R,hr,SurfaceRawEmbedding.ComplementCode.homology_finrank_le hc⟩

theorem evaluable_inFP (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (h : Evaluable ambient basis M U w) :
    (SurfaceRawEmbedding.evaluationProblem ambient basis M U w).InFP := by
  apply SurfaceRawEmbedding.evaluation_inFP_of ambient basis M U w
  let ei := SurfaceRawEmbedding.inputCode.restrict (SurfaceRawEmbedding.Input.Valid b u ambient)
  let view : {p:SurfaceRawEmbedding.Input // p.Valid b u ambient} → {p:Input // Valid b u ambient p} :=
    fun p => ⟨SurfaceRawEmbedding.graphRows p.val,graphRows_valid ambient p.property⟩
  have hp : FP ei SurfaceRawEmbedding.inputCode Subtype.val := fp_code_view _ _ _ (fun _ => rfl)
  have hv : FP ei (encoding.restrict (Valid b u ambient)) view :=
    (hp.comp SurfaceRawEmbedding.fp_graphRows).transportOutput (fun _ => rfl)
  exact (hv.comp h).congr (fun _ => rfl)

end PlanarHom.SurfaceRowEvaluation

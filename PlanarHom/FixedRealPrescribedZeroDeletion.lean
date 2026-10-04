import PlanarHom.FixedRealZeroWeightDeletion
import PlanarHom.MixedEvaluationFieldMap

/-! NEW: zero-weight deletion with separately prescribed smaller output field.
Every successful input encoding is preserved. Replies in either field may be
arbitrary valid representatives; the actual A.1 embedding/descent converters
are executed and their costs charged. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealZeroWeights
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit FixedRealExtension
variable {d e c f b u : ℕ} {K F C : Type} [Field K] [Field F] [Fintype C]
  [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F]
variable (ambient : Module.Basis (Fin e) (RationalFunction d) K)
  (small : Module.Basis (Fin f) (RationalFunction c) F) (embed : F →+* K)
variable (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
  (S : C → Prop) [Fintype {i // S i}] (hz : ∀ i, ¬S i → w i = 0)
  (N : Fin b → Matrix {i // S i} {i // S i} F)
  (V : Fin u → {i // S i} → F) (v : {i // S i} → F)
  (hM : ∀ l i j, embed (N l i j) = M l i.val j.val)
  (hU : ∀ l i, embed (V l i) = U l i.val)
  (hw : ∀ i, embed (v i) = w i.val)

include hz hM hU hw

theorem deleted_value_map (g : MixedCode) (hg : g.Valid b u) :
    embed (g.evaluate hg N V v) = g.evaluate hg M U w := by
  rw [map_evaluate]
  have hm : (fun l i j => embed (N l i j)) = (fun l i j => M l i.val j.val) :=
    funext (fun l => funext (fun i => funext (hM l i)))
  have hu : (fun l i => embed (V l i)) = (fun l i => U l i.val) :=
    funext (fun l => funext (hU l))
  have hv : (fun i => embed (v i)) = (fun i => w i.val) := funext hw
  rw [hm,hu,hv]
  exact (evaluate_restrict_zero_weights g hg M U w S hz).symm

private def mappedDeletion :
    Reduction (FixedRealComponents.problem ambient M U w)
      ((presentation ambient).problem MixedCode.encoding (PlanarValid b u)
        (fun g => embed (totalEvaluation N V v g))) := by
  apply queryReduction (presentation ambient) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid b u) (PlanarValid b u) (totalEvaluation M U w)
    (fun g => embed (totalEvaluation N V v g)) id (fp_id _) (fun _ h => h)
  intro g hg
  simp only [id_eq,totalEvaluation_valid _ _ _ g hg.1]
  exact deleted_value_map embed M U w S hz N V v hM hU hw g hg.1

private def mappedRestoration :
    Reduction ((presentation ambient).problem MixedCode.encoding (PlanarValid b u)
        (fun g => embed (totalEvaluation N V v g)))
      (FixedRealComponents.problem ambient M U w) := by
  apply queryReduction (presentation ambient) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid b u) (PlanarValid b u) (fun g => embed (totalEvaluation N V v g))
    (totalEvaluation M U w) id (fp_id _) (fun _ h => h)
  intro g hg
  simp only [id_eq,totalEvaluation_valid _ _ _ g hg.1]
  exact (deleted_value_map embed M U w S hz N V v hM hU hw g hg.1).symm

/-- Original evaluation reduces to the retained colors in their prescribed field. -/
def deletePrescribedReduction :
    Reduction (FixedRealComponents.problem ambient M U w) (FixedRealComponents.problem small N V v) :=
  (mappedDeletion ambient embed M U w S hz N V v hM hU hw).trans
    (FixedRealPresentationReductions.embeddingReduction ambient small embed MixedCode.encoding
      MixedCode.normalizer (PlanarValid b u) (totalEvaluation N V v))

/-- Conversely, exact A.1 descent recovers the smaller prescribed answer from
any valid answer representation of the original weighted source. -/
def restorePrescribedReduction :
    Reduction (FixedRealComponents.problem small N V v) (FixedRealComponents.problem ambient M U w) :=
  (FixedRealPresentationReductions.descentReduction ambient small embed MixedCode.encoding
      MixedCode.normalizer (PlanarValid b u) (totalEvaluation N V v)).trans
    (mappedRestoration ambient embed M U w S hz N V v hM hU hw)

end PlanarHom.FixedRealZeroWeights

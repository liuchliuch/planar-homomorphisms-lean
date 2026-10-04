import PlanarHom.FixedRealListProductCorrectness
import PlanarHom.RepresentedPresentationPipeline
import PlanarHom.GraphComponentSemantics

/-! Actual whole-input connected-component reduction in the represented field
model. It retains all mixed labels and isolates; the empty graph queries no
components and returns the represented empty product one. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealComponents
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
variable {n e b u:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def problem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : Problem :=
  (presentation basis).problem MixedCode.encoding (PlanarValid b u) (totalEvaluation M U w)

def connectedValid (g:MixedCode) : Prop :=
  g.PlanarValid b u ∧ (GraphComponentCode.support g).Connected ∧ 0<g.vertices

def connectedProblem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : Problem :=
  (presentation basis).problem MixedCode.encoding (connectedValid (b:=b) (u:=u)) (totalEvaluation M U w)

theorem represented_answers {Q:Type} (qs:List Q) (bs:List (Code n e)) (v:Q→K)
    (h:List.Forall₂ (fun q c=>Valid n c ∧ value basis c=v q) qs bs) :
    (∀c∈bs,Valid n c) ∧ bs.map (value basis)=qs.map v := by
  induction h with
  | nil=>simp
  | @cons q c qs bs hc hrest ih=>
    constructor
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hc.1
      · exact ih.1 a ha
    · simp only [List.map_cons]
      exact congrArg₂ List.cons hc.2 ih.2

def componentReduction (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    Reduction (problem basis M U w) (connectedProblem basis M U w) := by
  let prep:MixedCode→ℕ×List MixedCode:=fun g=>(0,GraphComponentCode.components g)
  let recov:ℕ×List (Code n e)→Code n e:=fun p=>FixedRealListProduct.product basis p.2
  have hp:FP MixedCode.encoding (BitEncoding.nat.prod MixedCode.encoding.list) prep:=
    (fp_const _ _ 0).pair GraphComponentMachines.fp_components
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n e) recov:=
    (PairProjectionMachines.fp_snd _ _).comp (FixedRealListProduct.fp_product basis)
  apply presentationPipeline (presentation basis) (presentation basis) MixedCode.encoding BitEncoding.nat
    MixedCode.encoding MixedCode.normalizer BitEncoding.natNormalizer (PlanarValid b u)
    (connectedValid (b:=b) (u:=u)) (totalEvaluation M U w) (totalEvaluation M U w) prep recov hp hr
  · exact GraphComponentCode.components_promises
  · intro g hg bs hbs
    have hb:=represented_answers basis (GraphComponentCode.components g) bs (totalEvaluation M U w) hbs
    refine ⟨FixedRealListProduct.product_valid basis bs hb.1,?_⟩
    change value basis (FixedRealListProduct.product basis bs)=totalEvaluation M U w g
    rw [FixedRealListProduct.product_value basis bs hb.1,hb.2,
      totalEvaluation_valid M U w g hg.1]
    exact (GraphComponentCode.evaluate_components g hg.1 M U w).symm

end PlanarHom.FixedRealComponents

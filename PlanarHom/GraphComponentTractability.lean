import PlanarHom.PromisePolynomialTime
import PlanarHom.GraphComponentReduction

/-! Genuine promised polynomial-time closure under the computed input-component
factorization. Components are produced by the existing machine, not supplied as
advice, and the output list is evaluated and multiplied by actual TM2 programs. -/
noncomputable section
open Classical
namespace PlanarHom.GraphComponentCode
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

/-- The connected-input promise carried by each computed query. -/
def connectedCodeValid (b u : ℕ) (g : MixedCode) : Prop :=
  g.PlanarValid b u ∧ (support g).Connected ∧ 0 < g.vertices

/-- The proved promise is attached without adding any serialized bits. -/
def promisedComponents (g : {g : MixedCode // g.PlanarValid b u}) :
    List {g : MixedCode // connectedCodeValid b u g} :=
  (components g.val).attachWith (connectedCodeValid b u) (components_promises g.val g.property)

/-- Computation and proof attachment produce exactly the original component
code list. In particular there is no decision procedure hidden in the subtype. -/
theorem fp_promisedComponents :
    FP (encoding.restrict (PlanarValid b u)) (encoding.restrict (connectedCodeValid b u)).list
      (promisedComponents (b:=b) (u:=u)) := by
  have h := (fp_code_view (encoding.restrict (PlanarValid b u)) encoding
    Subtype.val (fun _ => rfl)).comp GraphComponentMachines.fp_components
  apply h.transportOutput
  intro g
  simp [promisedComponents,BitEncoding.list,BitEncoding.restrict]

/-- A genuine connected promised computer extends to all planar occurrence
codes using actual component extraction, list execution, and field products.
Empty input uses an empty answer list and returns one. -/
theorem evaluation_inFP_of_connected (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (h : (connectedEvaluationProblem basis M U w).InFP) :
    (evaluationProblem basis M U w).InFP := by
  have hc : FP (encoding.restrict (connectedCodeValid b u)) (numberFieldEncoding basis)
      (fun g : {g : MixedCode // connectedCodeValid b u g} =>
        g.val.evaluate g.property.1.1 M U w) :=
    (restrictedEvaluation_inFP_iff basis M U w (connectedCodeValid b u) (fun _ hg => hg.1.1)).mp h
  have he := (fp_promisedComponents (b:=b) (u:=u)).comp
    (ListMapMachines.fp_map _ _ _ hc)
  have hp := he.comp (MaterializedFieldListMachines.fp_product basis)
  apply (evaluation_inFP_iff basis M U w).mpr
  apply hp.congr
  intro g
  rw [evaluate_components g.val g.property.1 M U w]
  apply congrArg List.prod
  simp only [Function.comp_apply,promisedComponents,List.map_attachWith]
  rw [← List.attach_map_val (l := components g.val) (f := totalEvaluation M U w)]
  apply List.map_congr_left
  intro c _
  exact (totalEvaluation_valid M U w c.val (components_promises g.val g.property c.val c.property).1.1).symm

/-- Restricting the all-planar promised computer to connected inputs costs no
new computation and supplies precisely the same values. -/
theorem connectedEvaluation_inFP_of_all (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (h : (evaluationProblem basis M U w).InFP) :
    (connectedEvaluationProblem basis M U w).InFP := by
  apply h.mono
  · rintro raw ⟨g,hd,hg⟩
    exact ⟨g,hd,hg.1⟩
  · intro _ _
    rfl

/-- Exact equivalence of the two genuine promised polynomial-time models. -/
theorem evaluation_inFP_iff_connected (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) :
    (evaluationProblem basis M U w).InFP ↔ (connectedEvaluationProblem basis M U w).InFP :=
  ⟨connectedEvaluation_inFP_of_all basis M U w,evaluation_inFP_of_connected basis M U w⟩

end PlanarHom.GraphComponentCode

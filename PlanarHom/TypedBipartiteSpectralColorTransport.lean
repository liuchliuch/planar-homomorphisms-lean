import PlanarHom.TypedBipartiteSpectralCompletion
import PlanarHom.MixedColorProblemEquivalence

/-! Sum-color and finite numeric color charts represent literally the same raw
promised problem. This connects the rational and effective spectral interfaces
without adding a computation, a domain label, or a new oracle presentation. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains
variable {C E K : Type} [Fintype C] [Fintype E] [Field K] [Algebra ℚ K]
variable {dimension bt ut dt : ℕ}

/-- Pull back intrinsic domains and all fixed constraints through one color
chart. The raw words, typing tables, output basis and values are identical. -/
theorem domainProblem_color_equiv (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C≃E) (M : Fin bt → Matrix E E K) (U : Fin ut → E → K) (w : E → K)
    (D : Fin dt → Set E) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) :
    domainEvaluationProblem basis (fun l i j=>M l (e i) (e j)) (fun l i=>U l (e i))
      (fun i=>w (e i)) (fun d=>e ⁻¹' D d) B T=
    domainEvaluationProblem basis M U w D B T := by
  have hu : extendedUnaries (fun l i=>U l (e i)) (fun d=>e ⁻¹' D d)=
      fun l i=>extendedUnaries U D l (e i) := by
    funext l i
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · simp [extendedUnaries]
    · simp [extendedUnaries,indicator]
  have hv := congrArg PromiseProblem.value
    (evaluationProblem_color_equiv basis e M (extendedUnaries U D) w)
  unfold domainEvaluationProblem
  congr 1
  rw [hu]
  exact hv

end PlanarHom.TypedBipartiteSpectral

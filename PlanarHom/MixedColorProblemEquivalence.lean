import PlanarHom.MixedColorEquivalence
import PlanarHom.MixedEvaluationPromises
noncomputable section
namespace PlanarHom.Complexity.MixedCode
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {dimension bt ut : ℕ}
theorem evaluationProblem_color_equiv (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C≃D) (M : Fin bt→Matrix D D K) (U : Fin ut→D→K) (w : D→K) :
    evaluationProblem basis (fun l i j=>M l (e i) (e j)) (fun l i=>U l (e i)) (fun i=>w (e i))=
      evaluationProblem basis M U w := by
  unfold evaluationProblem
  congr 1
  funext raw
  unfold evaluationValue
  split
  · rfl
  · rename_i g hg
    split
    · rename_i hv
      congr 1
      exact evaluate_color_equiv e g hv M U w
    · rfl
end PlanarHom.Complexity.MixedCode

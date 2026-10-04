import PlanarHom.FieldPresentationReductions

/-! A fixed bijection of colors leaves every raw evaluation value unchanged.
Its proof applies to all graph occurrences, loops, unaries and isolated vertices. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {bt ut dimension : ℕ}

theorem evaluate_colorReindex (e : C ≃ D) (g : MixedCode) (hg : g.Valid bt ut)
    (M : Fin bt → Matrix D D K) (U : Fin ut → D → K) (w : D → K) :
    g.evaluate hg (fun l i j => M l (e i) (e j)) (fun l i => U l (e i)) (fun i => w (e i))=
      g.evaluate hg M U w := by
  unfold evaluate
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin g.vertices => e))
  intro σ
  rfl

theorem evaluationProblem_colorReindex (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C ≃ D) (M : Fin bt → Matrix D D K) (U : Fin ut → D → K) (w : D → K) :
    evaluationProblem basis (fun l i j => M l (e i) (e j)) (fun l i => U l (e i)) (fun i => w (e i))=
      evaluationProblem basis M U w := by
  apply congrArg (PromiseProblem.mk (PlanarInput bt ut))
  funext raw
  unfold evaluationValue
  cases hd : encoding.decode raw with
  | none => rfl
  | some g =>
    by_cases hg : g.Valid bt ut
    · simp only [dif_pos hg,evaluate_colorReindex e g hg M U w]
    · simp only [dif_neg hg]

end PlanarHom.Complexity.MixedCode

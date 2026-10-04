import PlanarHom.PrescribedDomainReindexReduction

/-! NEW RECONSTRUCTION (2026-10-02). Exact color-coordinate transport of the
baseline graph codec and original number-field output codec. -/
noncomputable section
namespace PlanarHom.Complexity.MixedCode
open scoped BigOperators
variable {C D R : Type} [Fintype C] [Fintype D] [CommSemiring R]
variable {bt ut : ℕ}

/-- Color names are not encoded in a graph, so a bijection changes no raw input. -/
theorem evaluate_reindexColors (e : C ≃ D) (g : MixedCode) (hg : g.Valid bt ut)
    (M : Fin bt → Matrix D D R) (U : Fin ut → D → R) (w : D → R) :
    g.evaluate hg (fun l i j => M l (e i) (e j)) (fun l i => U l (e i)) (fun i => w (e i)) =
      g.evaluate hg M U w := by
  classical
  unfold evaluate
  apply Fintype.sum_equiv (Equiv.piCongrRight fun _ => e)
  intro σ
  rfl

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.PrescribedDomains
variable {C D R : Type} [CommSemiring R] {ut dt : ℕ}

theorem extendedUnaries_preimage (e : C → D) (U : Fin ut → D → R) (S : Fin dt → Set D) :
    extendedUnaries (fun l i => U l (e i)) (fun d => e ⁻¹' S d) =
      fun l i => extendedUnaries U S l (e i) := by
  funext l i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) l <;>
    simp only [extendedUnaries, Fin.addCases_left, Fin.addCases_right]
  all_goals rfl

end PlanarHom.PrescribedDomains

namespace PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {dimension bt ut dt : ℕ}

/-- Equality holds on every raw word, including malformed and noncanonical words,
with the same original coefficient field and the same basis encoding. -/
theorem evaluationValue_reindexColors (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C ≃ D) (M : Fin bt → Matrix D D K) (U : Fin ut → D → K) (w : D → K) :
    evaluationValue basis (fun l i j => M l (e i) (e j))
      (fun l i => U l (e i)) (fun i => w (e i)) = evaluationValue basis M U w := by
  funext bits
  unfold evaluationValue
  split
  · rfl
  · split
    · rw [evaluate_reindexColors]
    · rfl

/-- Complete promise-problem equality: typing and all ordinary labels stay fixed. -/
theorem domainEvaluationProblem_reindexColors (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C ≃ D) (M : Fin bt → Matrix D D K) (U : Fin ut → D → K) (w : D → K)
    (S : Fin dt → Set D) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) :
    domainEvaluationProblem basis (fun l i j => M l (e i) (e j))
      (fun l i => U l (e i)) (fun i => w (e i)) (fun d => e ⁻¹' S d) B T =
      domainEvaluationProblem basis M U w S B T := by
  unfold domainEvaluationProblem
  rw [extendedUnaries_preimage, evaluationValue_reindexColors]

/-- Coordinate transport requires no oracle simulation beyond the genuine
identity caller; both raw input and source field code are literally unchanged. -/
def domainColorReindexReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (e : C ≃ D) (M : Fin bt → Matrix D D K) (U : Fin ut → D → K) (w : D → K)
    (S : Fin dt → Set D) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun l i j => M l (e i) (e j))
        (fun l i => U l (e i)) (fun i => w (e i)) (fun d => e ⁻¹' S d) B T)
      (domainEvaluationProblem basis M U w S B T) := by
  rw [domainEvaluationProblem_reindexColors]
  let bound := domainEvaluationProblem_output_bound basis M U w S B T
  exact PromisePolyTimeTuringReduction.refl_of_output_bound _ (Classical.choose bound) (Classical.choose_spec bound)

end PlanarHom.Complexity.MixedCode

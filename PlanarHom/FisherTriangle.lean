import PlanarHom.IsingEvenSubgraph
import Mathlib.Tactic.FinCases

/-!
# The explicit three-terminal Fisher decoration

The three triangle edges are labelled by their opposite terminal. For a chosen
set of external edges, there is exactly one internal completion precisely when
an odd number of external terminals are matched. This is a statement about
actual edge occurrence subsets, not a supplied matching oracle.
-/

noncomputable section
open scoped BigOperators

namespace PlanarHom.Fisher

/-- The local Fisher triangle; edge `i` is opposite terminal `i`. -/
def triangle : MultiGraph (Fin 3) (Fin 3) where
  src e := if e = 0 then 1 else if e = 1 then 2 else 0
  dst e := if e = 0 then 2 else if e = 1 then 0 else 1

/-- Internal edge set compatible with the terminals already covered externally. -/
def TriangleCompatible (B M : Finset (Fin 3)) : Prop :=
  ∀ v : Fin 3, (M.filter (fun e => e ≠ v)).card + (if v ∈ B then 1 else 0) = 1

instance (B M : Finset (Fin 3)) : Decidable (TriangleCompatible B M) :=
  inferInstanceAs (Decidable (∀ v : Fin 3,
    (M.filter (fun e => e ≠ v)).card + (if v ∈ B then 1 else 0) = 1))

/-- One external terminal forces the opposite edge; three force no internal edge. -/
def triangleCompletion (B : Finset (Fin 3)) : Finset (Fin 3) :=
  if B.card = 1 then B else ∅

theorem triangle_completion_iff :
    ∀ B M : Finset (Fin 3), TriangleCompatible B M ↔
      Odd B.card ∧ M = triangleCompletion B := by
  decide +kernel

/-- In the even-subgraph reduction, an original edge is externally matched
precisely when it is absent from the selected even subgraph. -/
theorem triangle_even_completion_iff :
    ∀ A M : Finset (Fin 3), TriangleCompatible Aᶜ M ↔
      Even A.card ∧ M = triangleCompletion Aᶜ := by
  decide +kernel

open Classical

theorem triangle_incidence (e v : Fin 3) :
    ((if triangle.src e = v then 1 else 0 : ℕ) +
      (if triangle.dst e = v then 1 else 0)) = if e ≠ v then 1 else 0 := by
  revert e v
  decide +kernel

/-- The combinatorial gate is exactly the multigraph's ordinary incidence degree. -/
theorem triangle_selectedDegree (M : Finset (Fin 3)) (v : Fin 3) :
    triangle.selectedDegree M v = (M.filter (fun e => e ≠ v)).card := by
  unfold MultiGraph.selectedDegree
  calc
    _ = ∑ e ∈ M, if e ≠ v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      convert triangle_incidence e v using 1
      congr 1 <;> exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
    _ = _ := by exact Finset.sum_boole _ _

theorem triangleCompatible_iff_degree (B M : Finset (Fin 3)) :
    TriangleCompatible B M ↔
      ∀ v, triangle.selectedDegree M v + (if v ∈ B then 1 else 0) = 1 := by
  simp only [TriangleCompatible, triangle_selectedDegree]

/-- Unique internal matching completion with its precise parity criterion. -/
theorem existsUnique_triangleCompletion (B : Finset (Fin 3)) :
    (∃! M, ∀ v, triangle.selectedDegree M v + (if v ∈ B then 1 else 0) = 1) ↔
      Odd B.card := by
  simp_rw [← triangleCompatible_iff_degree, triangle_completion_iff]
  constructor
  · rintro ⟨M, ⟨h, _⟩, _⟩
    exact h
  · intro h
    exact ⟨triangleCompletion B, ⟨h, rfl⟩, fun _ hM => hM.2⟩

end PlanarHom.Fisher

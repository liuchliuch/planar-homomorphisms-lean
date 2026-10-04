import PlanarHom.RootedRestrictionReduction
import PlanarHom.AlgebraicProductInterpolation
import Mathlib.Algebra.Order.Field.Subfield

/-! Real-algebraic single-root restriction in the source language's original
number field, with a literal real assignment-sum interpretation. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.MultiGraph
local instance (priority := 10000) rootedRealAvailabilityDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V E C K L : Type} [Fintype V] [Fintype E] [Fintype C]
variable [CommSemiring K] [CommSemiring L]

theorem map_rootRestricted (φ : K →+* L) (G : MultiGraph V E) (r : V)
    (M : Matrix C C K) (w : C → K) (X : Set C) :
    φ (G.rootRestricted r M w X) =
      G.rootRestricted r (fun i j => φ (M i j)) (fun i => φ (w i)) X := by
  unfold rootRestricted
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ r ∈ X
  · simp [h,assignmentWeight,map_mul,map_prod]
  · simp [h]

end PlanarHom.MultiGraph
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q : ℕ} (L : RealLanguage q 1 0)

def singleRootProblem (X : Set (Fin q)) : PromiseProblem :=
  RootedRestriction.rootProblem L.basis (L.matricesK 0) L.weightsK X

/-- Source Lemma3.5's rooted computational conclusion; the component corollaries
are assembled separately. The original oracle is exactly the one fixed matrix
with its positive background vector. -/
def lemma35_root (hw : ∀ i, 0 < L.weights i) (X : Set (Fin q)) :
    PromisePolyTimeTuringReduction (L.singleRootProblem X) L.problem := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hwK : ∀ i, 0 < L.weightsK i := hw
  have h := RootedRestriction.rootReduction L.basis (L.matricesK 0) L.weightsK hwK X
  have hM : (fun _ : Fin 1 => L.matricesK 0) = L.matricesK := by
    funext l
    congr 1
    exact (Fin.eq_zero l).symm
  have hU : (fun u : Fin 0 => Fin.elim0 u) = L.unariesK := by
    funext u
    exact u.elim0
  rw [hM,hU] at h
  exact h

/-- The encoded answer represents the exact original real single-root sum,
including the original root weight once. -/
theorem rootRestricted_coe (g : MixedCode) (hg : g.Valid 1 0) (r : Fin g.vertices)
    (X : Set (Fin q)) :
    L.field.val ((g.toMultiGraph hg).rootRestricted r (L.matricesK 0) L.weightsK X) =
      (g.toMultiGraph hg).rootRestricted r (L.matrices 0) L.weights X :=
  MultiGraph.map_rootRestricted L.field.val.toRingHom _ r _ _ X

end PlanarHom.AlgebraicProductInterpolation.RealLanguage

import PlanarHom.RootedColorRestriction
import Mathlib.Data.Fintype.Quotient

/-! Exact decomposition over the numerical support components of a fixed
symmetric source matrix. No sign or positivity hypothesis enters the identity. -/
noncomputable section
open scoped BigOperators
open Classical

namespace PlanarHom.RootedRestriction
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K]

/-- A finite source has finitely many numerical support components, including
one singleton component for every isolated color. -/
instance supportComponentsFintype (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) :
    Fintype (colorSupport M hs).ConnectedComponent :=
  Fintype.ofSurjective (colorSupport M hs).connectedComponentMk (fun c => Quot.exists_rep c)

/-- Splitting the root color by its unique support component partitions the
entire assignment sum. This identity itself does not require connected input. -/
theorem partition_eq_sum_rootRestricted (g : MixedCode) (hg : g.Valid 1 0)
    (r : Fin g.vertices) (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K) :
    (g.toMultiGraph hg).partition M w =
      ∑ c : (colorSupport M hs).ConnectedComponent,
        (g.toMultiGraph hg).rootRestricted r M w c.supp := by
  unfold MultiGraph.partition MultiGraph.rootRestricted
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff]
  simp

/-- On a genuine connected input every nonzero assignment lies in the root's
numerical support component. Hence the value is the finite sum of the literal
color-submatrix values, even for signed matrices and zero interaction rows. -/
theorem partition_eq_sum_supportBlocks (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K) :
    (g.toMultiGraph hg).partition M w =
      ∑ c : (colorSupport M hs).ConnectedComponent,
        (g.toMultiGraph hg).partition (fun i j : c.supp => M i.val j.val)
          (fun i : c.supp => w i.val) := by
  rw [partition_eq_sum_rootRestricted g hg r M hs w]
  apply Finset.sum_congr rfl
  intro c _
  exact rootRestricted_eq_submatrix g hg hc r M hs w c.supp (component_colorClosed M hs c)

/-- The same identity in the raw homogeneous-code semantics used by the
number-field machines. A supplied positive vertex count chooses index zero. -/
theorem evaluate_eq_sum_supportBlocks (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (hn : 0 < g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K) :
    g.evaluate hg (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w =
      ∑ c : (colorSupport M hs).ConnectedComponent,
        g.evaluate hg (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
          (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val) := by
  simp_rw [evaluate_homogeneous]
  exact partition_eq_sum_supportBlocks g hg hc ⟨0,hn⟩ M hs w

end PlanarHom.RootedRestriction

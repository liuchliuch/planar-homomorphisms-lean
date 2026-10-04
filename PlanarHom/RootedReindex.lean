import PlanarHom.RootedPlanarity
import PlanarHom.IncidencePartition

/-! Every finite rooted presentation belongs to the one fixed family used in
weighted signature projection, independently of its chosen finite label types. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.RootedGraph
local instance (priority := 10000) rootedReindexDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V W E F C R : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
variable [Fintype C] [CommSemiring R]

def reindex (G : RootedGraph V E) (v : V ≃ W) (e : E ≃ F) : RootedGraph W F :=
  MultiGraph.reindex G (Equiv.sumCongr (Equiv.refl PUnit) v) e

@[simp] theorem signature_reindex (G : RootedGraph V E) (v : V ≃ W) (e : E ≃ F)
    (M : Matrix C C R) (w : C → R) (i : C) :
    signature (reindex G v e) M w i = signature G M w i := by
  symm
  unfold signature
  apply Fintype.sum_equiv (Equiv.arrowCongr v (Equiv.refl C))
  intro σ
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv v
    intro a
    simp [Equiv.arrowCongr]
  · apply Fintype.prod_equiv e
    intro a
    simp only [reindex, MultiGraph.reindex, Equiv.symm_apply_apply]
    congr 1
    · cases G.src a <;> simp [extend, Equiv.arrowCongr]
    · cases G.dst a <;> simp [extend, Equiv.arrowCongr]

/-- Canonical finite labels are only a presentation change, never a restriction
on the set of rooted graphs used by the projection theorem. -/
def finitePresentation (G : RootedGraph V E) (hG : G.Planar) : FiniteRootedPlanar :=
  ⟨Fintype.card V,Fintype.card E,reindex G (Fintype.equivFin V) (Fintype.equivFin E),
    (MultiGraph.planar_reindex_iff _ _ _).mpr hG⟩

@[simp] theorem signature_finitePresentation (G : RootedGraph V E) (hG : G.Planar)
    (M : Matrix C C R) (w : C → R) :
    FiniteRootedPlanar.signature (finitePresentation G hG) M w = signature G M w := by
  funext i
  exact signature_reindex G _ _ M w i

end PlanarHom.RootedGraph

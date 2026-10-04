import PlanarHom.PlanarTransport
import PlanarHom.Basic

/-! Exact weighted partition invariance under occurrence-preserving graph
reindexing. No edge or isolated vertex is discarded. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.MultiGraph
variable {V E W F C R : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable [Fintype C] [CommSemiring R] {G : MultiGraph V E} {H : MultiGraph W F}

omit [Fintype C] in
theorem IncidenceEquiv.assignmentWeight (i : IncidenceEquiv G H)
    (M : Matrix C C R) (w : C → R) (σ : V → C) :
    H.assignmentWeight M w (fun v => σ (i.vertex.symm v)) = G.assignmentWeight M w σ := by
  unfold MultiGraph.assignmentWeight
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv i.vertex.symm
    intro v
    rfl
  · apply Fintype.prod_equiv i.edge.symm
    intro e
    have hs : i.vertex.symm (H.src e) = G.src (i.edge.symm e) := (i.symm.src_eq e).symm
    have hd : i.vertex.symm (H.dst e) = G.dst (i.edge.symm e) := (i.symm.dst_eq e).symm
    simp only [hs, hd]

theorem IncidenceEquiv.partition (i : IncidenceEquiv G H)
    (M : Matrix C C R) (w : C → R) : H.partition M w = G.partition M w := by
  symm
  unfold MultiGraph.partition
  apply Fintype.sum_equiv (Equiv.arrowCongr i.vertex (Equiv.refl C))
  intro σ
  exact (i.assignmentWeight M w σ).symm

@[simp] theorem partition_reindex (G : MultiGraph V E) (v : V ≃ W) (e : E ≃ F)
    (M : Matrix C C R) (w : C → R) : (G.reindex v e).partition M w = G.partition M w :=
  (G.reindexEquiv v e).partition M w

end PlanarHom.MultiGraph

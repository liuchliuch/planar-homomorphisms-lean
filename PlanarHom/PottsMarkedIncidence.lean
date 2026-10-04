import PlanarHom.PottsMarkedCoefficientFilter
import PlanarHom.IncidencePartition

/-! Marked polynomial invariance under a literal incidence equivalence that
also preserves the designated long-edge occurrences. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph
variable {V E W F : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype F]

 theorem markedPolynomial_incidence {G : MultiGraph V E} {H : MultiGraph W F}
    (i : G.IncidenceEquiv H) (longG : Finset E) (longH : Finset F)
    (hlong : ∀e,e∈longG ↔ i.edge e∈longH) (q N : ℕ) :
    markedPolynomial G q longG N=markedPolynomial H q longH N := by
  unfold markedPolynomial
  rw [Fintype.card_congr i.vertex]
  congr 1
  apply Fintype.sum_equiv (Equiv.arrowCongr i.vertex (Equiv.refl (Fin q)))
  intro σ
  apply Fintype.prod_equiv i.edge
  intro e
  have hs : i.vertex.symm (H.src (i.edge e))=G.src e := by rw [i.src_eq,Equiv.symm_apply_apply]
  have ht : i.vertex.symm (H.dst (i.edge e))=G.dst e := by rw [i.dst_eq,Equiv.symm_apply_apply]
  simp only [Equiv.arrowCongr_apply,Equiv.coe_refl,Function.comp_apply,id_eq,hs,ht,← hlong]
end PlanarHom.PottsCentered

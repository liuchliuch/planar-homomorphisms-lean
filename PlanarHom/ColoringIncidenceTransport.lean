import PlanarHom.ThreeColorPaletteCounting
import PlanarHom.PlanarTransport

/-! Exact ordinary-coloring transport along incidence-preserving finite charts. -/
noncomputable section
namespace PlanarHom.MultiGraph.IncidenceEquiv
open ThreeColorPaletteCounting
variable {V E V' E' : Type} {G : MultiGraph V E} {H : MultiGraph V' E'}

def colorings (e : IncidenceEquiv G H) : Coloring G ≃ Coloring H where
  toFun col := ⟨col.val ∘ e.vertex.symm,by
    intro f
    change col.val (e.symm.vertex (H.src f))≠col.val (e.symm.vertex (H.dst f))
    rw [←e.symm.src_eq,←e.symm.dst_eq]
    exact col.property (e.edge.symm f)⟩
  invFun col := ⟨col.val ∘ e.vertex,by
    intro f
    change col.val (e.vertex (G.src f))≠col.val (e.vertex (G.dst f))
    rw [←e.src_eq,←e.dst_eq]
    exact col.property (e.edge f)⟩
  left_inv col := by
    apply Subtype.ext
    funext v
    exact congrArg col.val (e.vertex.symm_apply_apply v)
  right_inv col := by
    apply Subtype.ext
    funext v
    exact congrArg col.val (e.vertex.apply_symm_apply v)

theorem coloring_count [Fintype V] [Fintype E] [Fintype V'] [Fintype E'] (e : IncidenceEquiv G H) :
    ProperColoringPottsReduction.properColoringCount G 3=
      ProperColoringPottsReduction.properColoringCount H 3 := by
  rw [properCount_eq_natCard,properCount_eq_natCard]
  exact Nat.card_congr e.colorings

end PlanarHom.MultiGraph.IncidenceEquiv

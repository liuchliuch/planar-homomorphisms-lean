import PlanarHom.SurfaceRibbonComplement

/-! NEW genus budget from the actual gluing incidence graph. Disconnected
ribbon components and positive-genus complementary regions are both retained. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRibbonComplement
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G}

 theorem connected_componentCount_one {W F : Type*} [Fintype W] [Fintype F]
    (H : MultiGraph W F) (root : W) (h : ∀u v,H.componentSetoid Finset.univ u v) :
    H.componentCount Finset.univ=1 := by
  letI : Subsingleton (H.Components Finset.univ):=⟨by
    intro a b
    induction a using Quotient.inductionOn with | h a=>
      induction b using Quotient.inductionOn with | h b=>
        exact Quotient.sound (h a b)⟩
  letI : Nonempty (H.Components Finset.univ):=⟨Quotient.mk _ root⟩
  exact (Nat.card_eq_fintype_card (α:=H.Components Finset.univ)).symm.trans Nat.card_unique

 theorem Data.incidence_count (D : Data R) {g : ℕ} (h : D.Valid g) :
    D.incidence.componentCount Finset.univ=1 :=
  connected_componentCount_one D.incidence (.inr ⟨0,h.1⟩) h.2.1

 theorem Data.incidence_card_bound (D : Data R) {g : ℕ} (h : D.Valid g) :
    Fintype.card (Component (G:=G))+D.regions≤Fintype.card (Boundary R)+1 := by
  have hh:=D.incidence.vertices_le_card_add_componentCount Finset.univ
  rw [D.incidence_count h,Finset.card_univ,Fintype.card_sum,Fintype.card_fin] at hh
  exact hh

/-- The exact global ribbon Euler deficit is bounded by the ambient genus.
Unused handles consume budget through the nonnegative complement genera. -/
theorem Data.ribbon_deficit_bound (D : Data R) {g : ℕ} (h : D.Valid g) :
    Fintype.card E+2*Fintype.card (Component (G:=G))+
      2*(∑j,D.regionGenus j)≤Fintype.card V+Fintype.card (Boundary R)+2*g := by
  have hc:=D.incidence_card_bound h
  have he:=h.2.2
  omega

/-- Any genus read from the actual global capped-ribbon Euler equation obeys
the ambient bound. The equation is a derived rotation fact, not an input field. -/
theorem Data.capped_genus_bound (D : Data R) {g h : ℕ} (hd : D.Valid g)
    (he : Fintype.card V+Fintype.card (Boundary R)+2*h=
      Fintype.card E+2*Fintype.card (Component (G:=G))) :
    h+(∑j,D.regionGenus j)≤g := by
  have hb:=D.ribbon_deficit_bound hd
  omega

 theorem Data.capped_genus_le (D : Data R) {g h : ℕ} (hd : D.Valid g)
    (he : Fintype.card V+Fintype.card (Boundary R)+2*h=
      Fintype.card E+2*Fintype.card (Component (G:=G))) : h≤g := by
  have hh:=D.capped_genus_bound hd he
  omega

/-- The ordinary cycle rank of the actual connected boundary-incidence graph. -/
 def Data.incidenceCycleRank (D : Data R) : ℕ :=
  Fintype.card (Boundary R)+1-(Fintype.card (Component (G:=G))+D.regions)

 theorem Data.genus_decomposition (D : Data R) {g h : ℕ} (hd : D.Valid g)
    (he : Fintype.card V+Fintype.card (Boundary R)+2*h=
      Fintype.card E+2*Fintype.card (Component (G:=G))) :
    h+(∑j,D.regionGenus j)+D.incidenceCycleRank=g := by
  have hc:=D.incidence_card_bound hd
  have ha:=hd.2.2
  unfold Data.incidenceCycleRank
  omega

end PlanarHom.SurfaceRibbonComplement

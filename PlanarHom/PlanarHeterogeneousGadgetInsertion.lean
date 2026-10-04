import PlanarHom.PlanarGadgetInsertion

/-! NEW genuine geometric replacement by occurrence-dependent finite gadgets.
The private vertex/edge types may vary with each original occurrence. All old
vertices survive, and loop terminals may coincide in the host. -/
noncomputable section
namespace PlanarHom.MultiGraph

def insertFamilyVertex {V E : Type*} {W : E→Type*} (G : MultiGraph V E) (e : E) :
    Bool⊕W e → V⊕(Σ e,W e)
  | .inl false => .inl (G.src e)
  | .inl true => .inl (G.dst e)
  | .inr w => .inr ⟨e,w⟩

def insertFamily {V E : Type*} {W F : E→Type*} (G : MultiGraph V E)
    (K : ∀ e,TwoTerminal (W e) (F e)) : MultiGraph (V⊕(Σ e,W e)) (Σ e,F e) where
  src p := G.insertFamilyVertex p.1 ((K p.1).src p.2)
  dst p := G.insertFamilyVertex p.1 ((K p.1).dst p.2)

namespace RibbonDrawing
variable {V E : Type*} {W F : E→Type*} {G : MultiGraph V E}
    {K : ∀ e,TwoTerminal (W e) (F e)}

def insertFamilyPoint (d : RibbonDrawing G) (k : ∀ e,TwoTerminal.StripDrawing (K e)) :
    V⊕(Σ e,W e)→Plane :=
  Sum.elim d.point (fun p=>d.band p.1 ((k p.1).point (.inr p.2)))

theorem insertFamilyPoint_attach (d : RibbonDrawing G) (k : ∀ e,TwoTerminal.StripDrawing (K e))
    (e : E) (v : Bool⊕W e) :
    d.insertFamilyPoint k (G.insertFamilyVertex e v)=d.band e ((k e).point v) := by
  rcases v with (b|w)
  · cases b
    · simp [insertFamilyPoint,insertFamilyVertex,(k e).left,d.band_zero]
    · simp [insertFamilyPoint,insertFamilyVertex,(k e).right,d.band_one]
  · rfl

def insertFamilyDrawing (d : RibbonDrawing G) (k : ∀ e,TwoTerminal.StripDrawing (K e)) :
    PlaneDrawing (G.insertFamily K) where
  point := d.insertFamilyPoint k
  point_injective := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (d.point_injective h)
      | inr q => exact False.elim (d.band_avoids q.1 _ ((k q.1).internal_inside q.2) v h.symm)
    | inr p =>
      cases y with
      | inl w => exact False.elim (d.band_avoids p.1 _ ((k p.1).internal_inside p.2) w h)
      | inr q =>
        rcases p with ⟨e,w⟩
        rcases q with ⟨f,z⟩
        obtain ⟨he,hv⟩ := d.band_injective e f _ _
          ((k e).internal_inside w) ((k f).internal_inside z) h
        cases he
        have hw : w=z := Sum.inr.inj ((k e).point_injective hv)
        cases hw
        rfl
  curve p := (d.band p.1).comp ((k p.1).curve p.2)
  curve_zero p := by
    change d.band p.1 ((k p.1).curve p.2 0)=d.insertFamilyPoint k _
    rw [(k p.1).curve_zero,insertFamily,d.insertFamilyPoint_attach]
  curve_one p := by
    change d.band p.1 ((k p.1).curve p.2 1)=d.insertFamilyPoint k _
    rw [(k p.1).curve_one,insertFamily,d.insertFamilyPoint_attach]
  interior_injective := by
    rintro ⟨e,a⟩ ⟨f,b⟩ s t hs ht h
    obtain ⟨hef,hab⟩ := d.band_injective e f _ _
      ((k e).curve_inside a s hs) ((k f).curve_inside b t ht) h
    cases hef
    obtain ⟨hab,hst⟩ := (k e).interior_injective a b s t hs ht hab
    cases hab
    exact ⟨rfl,hst⟩
  interior_avoids := by
    rintro ⟨e,a⟩ t ht (v|⟨f,w⟩) h
    · exact d.band_avoids e _ ((k e).curve_inside a t ht) v h
    · obtain ⟨hef,hq⟩ := d.band_injective e f _ _
        ((k e).curve_inside a t ht) ((k f).internal_inside w) h
      cases hef
      exact (k e).interior_avoids a t ht (.inr w) hq

end RibbonDrawing

theorem Planar.insertFamily {V E : Type*} {W F : E→Type*}
    [Finite V] [Finite E] [∀ e,Finite (W e)] [∀ e,Finite (F e)]
    {G : MultiGraph V E} (hG : G.Planar) (K : ∀ e,TwoTerminal (W e) (F e))
    (hK : ∀ e,TwoTerminal.PlanarEdgeGadget (K e)) : (G.insertFamily K).Planar := by
  obtain ⟨d⟩ := hG.exists_ribbonDrawing
  exact ⟨d.insertFamilyDrawing (fun e=>Classical.choice (hK e).exists_stripDrawing)⟩

end PlanarHom.MultiGraph

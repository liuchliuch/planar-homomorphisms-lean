import PlanarHom.PlanarEmbedding

/-! Exact gluing of independently drawn finite-port graph pieces. The regions
are concrete geometric sets, which may include privately owned boundary rims;
there is no assumption of global planarity or an embedding oracle. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.PortPatchAssembly
open MultiGraph
variable {C B : Type} {P W E : C → Type}
variable (G : ∀ c,MultiGraph (P c ⊕ W c) (E c))
variable (d : ∀ c,PlaneDrawing (G c))
variable (region : C → Set Plane) (bpoint : B → Plane) (port : ∀ c,P c → B)

abbrev Vertex := B ⊕ Sigma W
abbrev Edge := Sigma E

def placeVertex (c : C) : P c ⊕ W c → Vertex (B := B) (W := W)
  | .inl k => .inl (port c k)
  | .inr w => .inr ⟨c,w⟩

def graph : MultiGraph (Vertex (B := B) (W := W)) (Edge (E := E)) where
  src e := placeVertex port e.1 ((G e.1).src e.2)
  dst e := placeVertex port e.1 ((G e.1).dst e.2)

def point : Vertex (B := B) (W := W) → Plane
  | .inl b => bpoint b
  | .inr w => (d w.1).point (.inr w.2)

variable (hd : Pairwise (fun c c' => Disjoint (region c) (region c')))
variable (hb : Function.Injective bpoint)
variable (hboundary : ∀ c b,bpoint b∉region c)
variable (hpoint : ∀ c w,(d c).point (.inr w)∈region c)
variable (hcurve : ∀ c e t,Inside t → (d c).curve e t∈region c)
variable (hport : ∀ c k,(d c).point (.inl k)=bpoint (port c k))

include hd in
private theorem region_index (c c' : C) (p : Plane) (hc : p∈region c) (hc' : p∈region c') : c=c' := by
  by_contra hne
  exact Set.disjoint_left.mp (hd hne) hc hc'

include hd hb hboundary hpoint in
theorem point_injective : Function.Injective (point G d bpoint) := by
  intro v w he
  cases v with
  | inl b =>
    cases w with
    | inl b' => exact congrArg Sum.inl (hb he)
    | inr w =>
      have hh := hpoint w.1 w.2
      change bpoint b=(d w.1).point (.inr w.2) at he
      rw [←he] at hh
      exact False.elim (hboundary w.1 b hh)
  | inr v =>
    cases w with
    | inl b =>
      have hh := hpoint v.1 v.2
      change (d v.1).point (.inr v.2)=bpoint b at he
      rw [he] at hh
      exact False.elim (hboundary v.1 b hh)
    | inr w =>
      have hv := hpoint v.1 v.2
      have hw := hpoint w.1 w.2
      change (d v.1).point (.inr v.2)=(d w.1).point (.inr w.2) at he
      rw [←he] at hw
      have hi := region_index region hd _ _ _ hv hw
      rcases v with ⟨c,v⟩
      rcases w with ⟨c',w⟩
      dsimp only at hi
      subst c'
      have heq : v=w := Sum.inr.inj ((d c).point_injective he)
      subst w
      rfl

include hport in
theorem point_place (c : C) (v : P c ⊕ W c) :
    point G d bpoint (placeVertex port c v)=(d c).point v := by
  cases v with
  | inl k => exact (hport c k).symm
  | inr w => rfl

/-- The exact global curves are the constituent curves, sharing only authorized
port vertices; every edge occurrence keeps its own sigma index. -/
def drawing : PlaneDrawing (graph G port) where
  point := point G d bpoint
  point_injective := point_injective G d region bpoint hd hb hboundary hpoint
  curve e := (d e.1).curve e.2
  curve_zero e := by
    rw [(d e.1).curve_zero]
    exact (point_place G d bpoint port hport e.1 _).symm
  curve_one e := by
    rw [(d e.1).curve_one]
    exact (point_place G d bpoint port hport e.1 _).symm
  interior_injective := by
    rintro ⟨c,e⟩ ⟨c',f⟩ s t hs ht he
    have hs' := hcurve c e s hs
    have ht' := hcurve c' f t ht
    change (d c).curve e s=(d c').curve f t at he
    rw [←he] at ht'
    have hi := region_index region hd _ _ _ hs' ht'
    subst c'
    obtain ⟨hef,hst⟩ := (d c).interior_injective e f s t hs ht he
    exact ⟨by subst f; rfl,hst⟩
  interior_avoids := by
    rintro ⟨c,e⟩ t ht (b | ⟨c',w⟩) he
    · have hh := hcurve c e t ht
      change (d c).curve e t=bpoint b at he
      rw [he] at hh
      exact hboundary c b hh
    · have hs := hcurve c e t ht
      have hw := hpoint c' w
      change (d c).curve e t=(d c').point (.inr w) at he
      rw [←he] at hw
      have hi := region_index region hd _ _ _ hs hw
      subst c'
      exact (d c).interior_avoids e t ht (.inr w) he

end PlanarHom.PortPatchAssembly

import PlanarHom.PlanarNeighborhoods
import PlanarHom.PolygonalAttachments

/-!
# Explicit edge augmentation and contraction through a geometric collapse

An added edge is an actual injective curve disjoint from the existing support.
The contraction constructor uses an explicit continuous plane map and its exact
fibers, rather than a planarity-preservation premise. Existence of such a collapse
for an arbitrary embedded edge is not asserted in this module.
-/

noncomputable section
open Set unitInterval
open Classical
namespace PlanarHom.MultiGraph
variable {V E : Type*} (G : MultiGraph V E)

/-- Add one new occurrence, retaining every old occurrence and vertex. -/
def withEdge (u v : V) : MultiGraph V (E ⊕ Unit) where
  src := Sum.elim G.src (fun _ => u)
  dst := Sum.elim G.dst (fun _ => v)

namespace PlaneDrawing
variable {G}

/-- Assemble a genuine added curve with the existing drawing. -/
def withEdge (d : PlaneDrawing G) {u v : V} (p : Path (d.point u) (d.point v))
    (hp : Function.Injective p)
    (havoid : ∀ t, Inside t → p t ∉ d.support) : PlaneDrawing (G.withEdge u v) where
  point := d.point
  point_injective := d.point_injective
  curve := Sum.elim d.curve (fun _ => p.toContinuousMap)
  curve_zero := by rintro (e | e); exact d.curve_zero e; exact p.source
  curve_one := by rintro (e | e); exact d.curve_one e; exact p.target
  interior_injective := by
    rintro (e | e) (f | f) s t hs ht heq
    · obtain ⟨hef,hst⟩ := d.interior_injective e f s t hs ht heq
      exact ⟨congrArg Sum.inl hef,hst⟩
    · exact (havoid t ht (Or.inr (Set.mem_iUnion.mpr ⟨e,s,heq⟩))).elim
    · exact (havoid s hs (Or.inr (Set.mem_iUnion.mpr ⟨f,t,heq.symm⟩))).elim
    · exact ⟨congrArg Sum.inr (Subsingleton.elim _ _),hp heq⟩
  interior_avoids := by
    rintro (e | e) t ht w h
    · exact d.interior_avoids e t ht w h
    · exact havoid t ht (Or.inl ⟨w,h.symm⟩)

/-- A retained edge interior never meets a different edge, even at its endpoints. -/
theorem interior_notMem_other_range (d : PlaneDrawing G) {e f : E} (hef : e ≠ f)
    {t : I} (ht : Inside t) : d.curve e t ∉ Set.range (d.curve f) := by
  rintro ⟨s,hs⟩
  by_cases hs0 : s = 0
  · rw [hs0,d.curve_zero] at hs
    exact d.interior_avoids e t ht _ hs.symm
  by_cases hs1 : s = 1
  · rw [hs1,d.curve_one] at hs
    exact d.interior_avoids e t ht _ hs.symm
  exact hef (d.interior_injective e f t s ht (inside_of_ne_endpoints hs0 hs1) hs.symm).1

/-- The vertices contained in an edge range are precisely its endpoint vertices. -/
theorem point_mem_curve_range_iff (d : PlaneDrawing G) (v : V) (e : E) :
    d.point v ∈ Set.range (d.curve e) ↔ v = G.src e ∨ v = G.dst e := by
  constructor
  · rintro ⟨t,ht⟩
    rcases (d.curve_eq_point_iff e t v).mp ht with ⟨_,hv⟩ | ⟨_,hv⟩
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  · rintro (rfl | rfl)
    · exact ⟨0,d.curve_zero e⟩
    · exact ⟨1,d.curve_one e⟩

end PlaneDrawing

/-- Identify the destination with the source of a nonloop edge, deleting only
that occurrence. Other parallel occurrences consequently become loops. -/
def contractVertex (e : E) (hne : G.src e ≠ G.dst e) (v : V) :
    {w : V // w ≠ G.dst e} :=
  if h : v = G.dst e then ⟨G.src e,hne⟩ else ⟨v,h⟩

/-- Concrete endpoint/occurrence presentation of a nonloop edge contraction. -/
def contractEdge (e : E) (hne : G.src e ≠ G.dst e) :
    MultiGraph {v : V // v ≠ G.dst e} {f : E // f ≠ e} where
  src f := G.contractVertex e hne (G.src f.1)
  dst f := G.contractVertex e hne (G.dst f.1)

namespace PlaneDrawing
variable {G}

/-- An explicit geometric collapse has just one nonsingleton fiber: the selected
closed edge curve. All other plane points remain separated. -/
structure EdgeCollapse (d : PlaneDrawing G) (e : E) where
  map : C(Plane,Plane)
  fibers : ∀ x y, map x = map y ↔ x = y ∨
    (x ∈ Set.range (d.curve e) ∧ y ∈ Set.range (d.curve e))

namespace EdgeCollapse
variable {d : PlaneDrawing G} {e : E} (C : d.EdgeCollapse e)

theorem endpoints : C.map (d.point (G.src e)) = C.map (d.point (G.dst e)) :=
  (C.fibers _ _).mpr (Or.inr ⟨⟨0,d.curve_zero e⟩,⟨1,d.curve_one e⟩⟩)

theorem point_contractVertex (hne : G.src e ≠ G.dst e) (v : V) :
    C.map (d.point (G.contractVertex e hne v).1) = C.map (d.point v) := by
  by_cases h : v = G.dst e
  · subst v
    simpa [contractVertex] using C.endpoints
  · simp [contractVertex,h]

/-- Actual contraction drawing, including loops created from parallel edges. -/
def drawing (hne : G.src e ≠ G.dst e) : PlaneDrawing (G.contractEdge e hne) where
  point v := C.map (d.point v.1)
  point_injective := by
    intro v w h
    rcases (C.fibers _ _).mp h with h | ⟨hv,hw⟩
    · exact Subtype.ext (d.point_injective h)
    · have hv' : v.1 = G.src e :=
        ((d.point_mem_curve_range_iff _ _).mp hv).resolve_right v.2
      have hw' : w.1 = G.src e :=
        ((d.point_mem_curve_range_iff _ _).mp hw).resolve_right w.2
      exact Subtype.ext (hv'.trans hw'.symm)
  curve f := C.map.comp (d.curve f.1)
  curve_zero f := by
    change C.map (d.curve f.1 0) = C.map (d.point (G.contractVertex e hne (G.src f.1)).1)
    rw [d.curve_zero,C.point_contractVertex]
  curve_one f := by
    change C.map (d.curve f.1 1) = C.map (d.point (G.contractVertex e hne (G.dst f.1)).1)
    rw [d.curve_one,C.point_contractVertex]
  interior_injective := by
    intro f g s t hs ht h
    rcases (C.fibers _ _).mp h with heq | ⟨hf,_⟩
    · obtain ⟨hfg,hst⟩ := d.interior_injective _ _ s t hs ht heq
      exact ⟨Subtype.ext hfg,hst⟩
    · exact (d.interior_notMem_other_range f.2 hs hf).elim
  interior_avoids := by
    intro f t ht v h
    rcases (C.fibers _ _).mp h with heq | ⟨hf,_⟩
    · exact d.interior_avoids _ t ht _ heq
    · exact d.interior_notMem_other_range f.2 ht hf

end EdgeCollapse
end PlaneDrawing
end PlanarHom.MultiGraph

import PlanarHom.PlanarEmbedding
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions.SumProd

/-!
# Ordinary graph-realization semantics for the plane-drawing predicate

The geometric realization is the topological quotient of the disjoint union of
one singleton for every vertex and one closed unit interval for every edge,
identifying just each interval's endpoints with its incident vertices. Loops and
parallel occurrences are retained. We prove that a finite incidence multigraph
has a `PlaneDrawing` exactly when this usual realization embeds topologically in
`ℝ × ℝ`. Thus the drawing predicate is not a strengthened polygonal or embedded-
input notion of planarity.
-/

noncomputable section
open Set unitInterval Topology

namespace PlanarHom.MultiGraph
namespace Realization

variable {V E : Type*} (G : MultiGraph V E)

/-- Raw cells with their disjoint-union topology. Sigma indices are discrete by
the topology of a disjoint union, and do not require a topology on vertex labels. -/
abbrev Cells := (Σ _ : V, Unit) ⊕ (Σ _ : E, I)

/-- Labels of points after the endpoint identifications. This type is only used
to specify the equivalence relation; the realization has the quotient topology. -/
abbrev Core := V ⊕ (E × {t : I // Inside t})

private theorem inside_of_ne {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) : Inside t := by
  constructor
  · exact lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))

/-- Identify an edge endpoint with exactly its incidence vertex. -/
def tag : Cells (V := V) (E := E) → Core (V := V) (E := E)
  | Sum.inl ⟨v,_⟩ => Sum.inl v
  | Sum.inr ⟨e,t⟩ =>
    if h0 : t = 0 then Sum.inl (G.src e)
    else if h1 : t = 1 then Sum.inl (G.dst e)
    else Sum.inr (e, ⟨t, inside_of_ne h0 h1⟩)

/-- No identifications other than endpoint incidence. -/
def cellSetoid : Setoid (Cells (V := V) (E := E)) := Setoid.ker (Realization.tag G)

/-- Usual topological realization of the incidence multigraph. -/
abbrev Space := Quotient (Realization.cellSetoid G)


/-- Canonical vertex inclusion. -/
def vertex (v : V) : (Realization.Space G) := Quotient.mk (Realization.cellSetoid G) (Sum.inl ⟨v,()⟩)

/-- Canonical edge-interval map into the realization. -/
def edge (e : E) : C(I, (Realization.Space G)) where
  toFun t := Quotient.mk (Realization.cellSetoid G) (Sum.inr ⟨e,t⟩)
  continuous_toFun := continuous_quotient_mk'.comp
    (continuous_inr.comp continuous_sigmaMk)

@[simp] theorem edge_zero (e : E) : (Realization.edge G) e 0 = (Realization.vertex G) (G.src e) := by
  apply Quotient.sound
  change tag G _ = tag G _
  simp [tag]

@[simp] theorem edge_one (e : E) : (Realization.edge G) e 1 = (Realization.vertex G) (G.dst e) := by
  apply Quotient.sound
  change tag G _ = tag G _
  simp [tag]

theorem vertex_injective : Function.Injective (Realization.vertex G) := by
  intro v w h
  have hh := Quotient.exact h
  change tag G (Sum.inl ⟨v,()⟩) = tag G (Sum.inl ⟨w,()⟩) at hh
  exact Sum.inl.inj hh

theorem edge_interior_injective (e f : E) (s t : I) (hs : Inside s) (ht : Inside t)
    (h : (Realization.edge G) e s = (Realization.edge G) f t) : e = f ∧ s = t := by
  have hs0 : s ≠ 0 := fun h => by simp [h, Inside] at hs
  have hs1 : s ≠ 1 := fun h => by simp [h, Inside] at hs
  have ht0 : t ≠ 0 := fun h => by simp [h, Inside] at ht
  have ht1 : t ≠ 1 := fun h => by simp [h, Inside] at ht
  have hh := Quotient.exact h
  change (Realization.tag G) (Sum.inr ⟨e,s⟩) = (Realization.tag G) (Sum.inr ⟨f,t⟩) at hh
  simp only [tag, hs0, hs1, ht0, ht1, ↓reduceDIte, Sum.inr.injEq, Prod.mk.injEq] at hh
  exact ⟨hh.1, congrArg Subtype.val hh.2⟩

theorem edge_interior_avoids (e : E) (t : I) (ht : Inside t) (v : V) :
    (Realization.edge G) e t ≠ (Realization.vertex G) v := by
  intro h
  have ht0 : t ≠ 0 := fun h => by simp [h, Inside] at ht
  have ht1 : t ≠ 1 := fun h => by simp [h, Inside] at ht
  have hh := Quotient.exact h
  change (Realization.tag G) (Sum.inr ⟨e,t⟩) = (Realization.tag G) (Sum.inl ⟨v,()⟩) at hh
  simp [tag, ht0, ht1] at hh

end Realization

namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Interpret point labels in a drawing. -/
def coreMap (d : PlaneDrawing G) : Realization.Core (V := V) (E := E) → Plane :=
  Sum.elim d.point (fun p => d.curve p.1 p.2.1)

theorem coreMap_injective (d : PlaneDrawing G) : Function.Injective d.coreMap := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl (d.point_injective h)
    | inr q => exact False.elim (d.interior_avoids q.1 q.2.1 q.2.2 v h.symm)
  | inr p =>
    cases y with
    | inl w => exact False.elim (d.interior_avoids p.1 p.2.1 p.2.2 w h)
    | inr q =>
      obtain ⟨he,ht⟩ := d.interior_injective p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2 h
      exact congrArg Sum.inr (Prod.ext he (Subtype.ext ht))

/-- Draw every raw cell before taking the endpoint quotient. -/
def cellMap (d : PlaneDrawing G) : Realization.Cells (V := V) (E := E) → Plane
  | Sum.inl ⟨v,_⟩ => d.point v
  | Sum.inr ⟨e,t⟩ => d.curve e t

theorem cellMap_eq (d : PlaneDrawing G) (x : Realization.Cells (V := V) (E := E)) :
    d.cellMap x = d.coreMap ((Realization.tag G) x) := by
  rcases x with (⟨v,u⟩ | ⟨e,t⟩)
  · rfl
  · by_cases h0 : t = 0
    · simp [Realization.tag, h0, coreMap, cellMap, d.curve_zero]
    · by_cases h1 : t = 1
      · simp [Realization.tag, h1, coreMap, cellMap, d.curve_one]
      · simp [Realization.tag, h0, h1, coreMap, cellMap]

theorem continuous_cellMap (d : PlaneDrawing G) : Continuous d.cellMap := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_sigma fun _ => continuous_const
  · exact continuous_sigma fun e => (d.curve e).continuous

/-- Continuous map on the genuine topological realization. -/
def realizationMap (d : PlaneDrawing G) : C((Realization.Space G), Plane) where
  toFun := Quotient.lift d.cellMap (by
    intro a b h
    rw [d.cellMap_eq a, d.cellMap_eq b]
    exact congrArg d.coreMap h)
  continuous_toFun := d.continuous_cellMap.quotient_lift _

theorem realizationMap_injective (d : PlaneDrawing G) :
    Function.Injective d.realizationMap := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  apply Quotient.sound
  apply d.coreMap_injective
  simpa only [← cellMap_eq] using h

/-- Finiteness is used here: the graph realization is compact, so a continuous
injection into the Hausdorff plane is a topological embedding. -/
theorem isEmbedding_realizationMap [Finite V] [Finite E] (d : PlaneDrawing G) :
    IsEmbedding d.realizationMap :=
  (d.realizationMap.continuous.isClosedEmbedding d.realizationMap_injective).isEmbedding

end PlaneDrawing

/-- Planarity via topological embedding of the usual endpoint-glued realization. -/
def TopologicallyPlanar {V E : Type*} (G : MultiGraph V E) : Prop :=
  ∃ f : (Realization.Space G) → Plane, IsEmbedding f

/-- Any actual embedding of the realization gives the elementary plane-drawing
conditions. This direction does not need finite vertex or edge sets. -/
def drawingOfEmbedding {V E : Type*} {G : MultiGraph V E}
    (f : (Realization.Space G) → Plane) (hf : IsEmbedding f) : PlaneDrawing G where
  point v := f ((Realization.vertex G) v)
  point_injective := hf.injective.comp (Realization.vertex_injective G)
  curve e := ⟨f ∘ (Realization.edge G) e, hf.continuous.comp ((Realization.edge G) e).continuous⟩
  curve_zero e := congrArg f ((Realization.edge_zero G) e)
  curve_one e := congrArg f ((Realization.edge_one G) e)
  interior_injective e g s t hs ht h :=
    (Realization.edge_interior_injective G) e g s t hs ht (hf.injective h)
  interior_avoids e t ht v h := (Realization.edge_interior_avoids G) e t ht v (hf.injective h)

/-- Exact bridge to ordinary topological graph planarity, including loops,
parallel occurrences, disconnected graphs and isolated vertices. -/
theorem planar_iff_topologicallyPlanar {V E : Type*} [Finite V] [Finite E]
    (G : MultiGraph V E) : G.Planar ↔ G.TopologicallyPlanar := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.realizationMap, d.isEmbedding_realizationMap⟩
  · rintro ⟨f,hf⟩
    exact ⟨drawingOfEmbedding f hf⟩

end PlanarHom.MultiGraph

import PlanarHom.Gadgets
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
# Plane drawings of multigraphs, including loops

`PlaneDrawing` is a direct topological drawing: vertices are distinct plane points,
each edge occurrence is a continuous interval curve, and open edge interiors
are pairwise disjoint, injective, and avoid every vertex. The two endpoints of
one edge may coincide, so loops are represented correctly. `Planar` existentially
quantifies the drawing and does not change the input into an embedded graph.

Faces are actual connected components of the complement of the drawing;
cofaciality uses closure, and the outer-face version requires an unbounded face.

Subdivision is constructed by restricting the original curves to their two
halves. Edge ribbons are separately defined geometric certificates. Their
constructions imply ordinary plane drawings, but no equivalence between arbitrary
plane drawings and ribbon certificates is claimed in this file. The finite-graph
bridge is proved in PlanarRibbonExistence.lean (planar_iff_ribbonDrawing).
-/

noncomputable section
open Set unitInterval

namespace PlanarHom
namespace MultiGraph

abbrev Plane := ℝ × ℝ

/-- The open part of the closed unit interval. -/
def Inside (t : I) : Prop := (0 : ℝ) < t ∧ (t : ℝ) < 1

/-- An ordinary crossing-free plane drawing, with a separate curve for every
edge occurrence. Interior injectivity also rules out self-crossings of loops. -/
structure PlaneDrawing {V E : Type*} (G : MultiGraph V E) where
  point : V → Plane
  point_injective : Function.Injective point
  curve : E → C(I, Plane)
  curve_zero : ∀ e, curve e 0 = point (G.src e)
  curve_one : ∀ e, curve e 1 = point (G.dst e)
  interior_injective : ∀ e f s t, Inside s → Inside t →
    curve e s = curve f t → e = f ∧ s = t
  interior_avoids : ∀ e t, Inside t → ∀ v, curve e t ≠ point v

/-- Planarity of the abstract incidence graph. No embedding is input data. -/
def Planar {V E : Type*} (G : MultiGraph V E) : Prop := Nonempty (PlaneDrawing G)

namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- All vertices, including isolated ones, and all points of edge curves. -/
def support (d : PlaneDrawing G) : Set Plane :=
  Set.range d.point ∪ ⋃ e, Set.range (d.curve e)

/-- Terminals incident to one actual complementary face. -/
def Cofacial (d : PlaneDrawing G) (u v : V) : Prop :=
  ∃ z ∉ d.support,
    d.point u ∈ closure (connectedComponentIn d.supportᶜ z) ∧
    d.point v ∈ closure (connectedComponentIn d.supportᶜ z)

/-- The same face is unbounded, as required for a planar edge gadget. -/
def OuterCofacial (d : PlaneDrawing G) (u v : V) : Prop :=
  ∃ z ∉ d.support,
    ¬ Bornology.IsBounded (connectedComponentIn d.supportᶜ z) ∧
    d.point u ∈ closure (connectedComponentIn d.supportᶜ z) ∧
    d.point v ∈ closure (connectedComponentIn d.supportᶜ z)

theorem OuterCofacial.cofacial {d : PlaneDrawing G} {u v : V}
    (h : d.OuterCofacial u v) : d.Cofacial u v := by
  obtain ⟨z, hz, _, hu, hv⟩ := h
  exact ⟨z, hz, hu, hv⟩

theorem Cofacial.symm {d : PlaneDrawing G} {u v : V}
    (h : d.Cofacial u v) : d.Cofacial v u := by
  obtain ⟨z, hz, hu, hv⟩ := h
  exact ⟨z, hz, hv, hu⟩

theorem OuterCofacial.symm {d : PlaneDrawing G} {u v : V}
    (h : d.OuterCofacial u v) : d.OuterCofacial v u := by
  obtain ⟨z, hz, hb, hu, hv⟩ := h
  exact ⟨z, hz, hb, hv, hu⟩

end PlaneDrawing

/-- Subdivide every edge occurrence once. Each loop becomes two distinct edges
between its old vertex and its own new midpoint vertex. -/
def subdivide {V E : Type*} (G : MultiGraph V E) : MultiGraph (V ⊕ E) (E × Bool) where
  src p := if p.2 then Sum.inr p.1 else Sum.inl (G.src p.1)
  dst p := if p.2 then Sum.inl (G.dst p.1) else Sum.inr p.1

namespace PlaneDrawing

/-- Midpoint in the parameter interval. -/
def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem half_inside : Inside half := by norm_num [Inside, half]

/-- The left and right affine interval embeddings. -/
def halfParameter (b : Bool) : C(I, I) where
  toFun t := if b then
    ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
    else ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

@[simp] theorem halfParameter_false_zero : halfParameter false 0 = 0 := by
  apply Subtype.ext; norm_num [halfParameter]
@[simp] theorem halfParameter_false_one : halfParameter false 1 = half := by
  apply Subtype.ext; norm_num [halfParameter, half]
@[simp] theorem halfParameter_true_zero : halfParameter true 0 = half := by
  apply Subtype.ext; norm_num [halfParameter, half]
@[simp] theorem halfParameter_true_one : halfParameter true 1 = 1 := by
  apply Subtype.ext; norm_num [halfParameter]

theorem halfParameter_inside (b : Bool) {t : I} (ht : Inside t) :
    Inside (halfParameter b t) := by
  rcases ht with ⟨ht0, ht1⟩
  cases b <;> dsimp [Inside, halfParameter] <;> constructor <;> linarith

theorem halfParameter_injective {b c : Bool} {s t : I}
    (hs : Inside s) (ht : Inside t)
    (h : halfParameter b s = halfParameter c t) : b = c ∧ s = t := by
  have hh := congrArg (fun x : I => (x : ℝ)) h
  rcases hs with ⟨hs0, hs1⟩
  rcases ht with ⟨ht0, ht1⟩
  cases b <;> cases c <;> dsimp [halfParameter] at hh
  · exact ⟨rfl, Subtype.ext (by linarith)⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨rfl, Subtype.ext (by linarith)⟩

theorem halfParameter_ne_half (b : Bool) {t : I} (ht : Inside t) :
    halfParameter b t ≠ half := by
  intro h
  have hh := congrArg (fun x : I => (x : ℝ)) h
  rcases ht with ⟨ht0, ht1⟩
  cases b <;> dsimp [halfParameter, half] at hh <;> linarith

variable {V E : Type*} {G : MultiGraph V E}

/-- Subdivision reuses the given plane curves, so requires no perturbation or
tameness assumption. -/
def subdivide (d : PlaneDrawing G) : PlaneDrawing G.subdivide where
  point := Sum.elim d.point (fun e => d.curve e half)
  point_injective := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (d.point_injective h)
      | inr y => exact False.elim (d.interior_avoids y half half_inside x h.symm)
    | inr x =>
      cases y with
      | inl y => exact False.elim (d.interior_avoids x half half_inside y h)
      | inr y => exact congrArg Sum.inr (d.interior_injective x y half half
          half_inside half_inside h).1
  curve p := (d.curve p.1).comp (halfParameter p.2)
  curve_zero := by rintro ⟨e, b⟩; cases b <;> simp [MultiGraph.subdivide, d.curve_zero]
  curve_one := by rintro ⟨e, b⟩; cases b <;> simp [MultiGraph.subdivide, d.curve_one]
  interior_injective := by
    rintro ⟨e,b⟩ ⟨f,c⟩ s t hs ht h
    obtain ⟨hef, hst⟩ := d.interior_injective e f _ _
      (halfParameter_inside b hs) (halfParameter_inside c ht) h
    obtain ⟨hbc, hst'⟩ := halfParameter_injective hs ht hst
    exact ⟨Prod.ext hef hbc, hst'⟩
  interior_avoids := by
    rintro ⟨e,b⟩ t ht (v | f) h
    · exact d.interior_avoids e _ (halfParameter_inside b ht) v h
    · have heq := (d.interior_injective e f _ half
        (halfParameter_inside b ht) half_inside h).2
      exact halfParameter_ne_half b ht heq

/-- Every original parameter belongs to at least one half. -/
theorem exists_halfParameter (t : I) : ∃ b s, halfParameter b s = t := by
  by_cases ht : (t : ℝ) ≤ 1/2
  · refine ⟨false, ⟨2 * (t : ℝ), ?_⟩, ?_⟩
    · constructor <;> linarith [t.2.1]
    · apply Subtype.ext; dsimp [halfParameter]; ring
  · refine ⟨true, ⟨2 * (t : ℝ) - 1, ?_⟩, ?_⟩
    · constructor <;> linarith [t.2.2]
    · apply Subtype.ext; dsimp [halfParameter]; ring

/-- Subdivision changes incidence data but not the subset drawn in the plane. -/
@[simp] theorem support_subdivide (d : PlaneDrawing G) :
    d.subdivide.support = d.support := by
  ext x
  simp only [support, Set.mem_union, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro (⟨v,hv⟩ | ⟨⟨e,b⟩,t,ht⟩)
    · cases v with
      | inl v => exact Or.inl ⟨v,hv⟩
      | inr e => exact Or.inr ⟨e,half,hv⟩
    · exact Or.inr ⟨e,halfParameter b t,ht⟩
  · rintro (⟨v,hv⟩ | ⟨e,t,ht⟩)
    · exact Or.inl ⟨Sum.inl v,hv⟩
    · obtain ⟨b,s,hs⟩ := exists_halfParameter t
      exact Or.inr ⟨(e,b),s,by simpa [subdivide, hs] using ht⟩

@[simp] theorem cofacial_subdivide_iff (d : PlaneDrawing G) (u v : V) :
    d.subdivide.Cofacial (Sum.inl u) (Sum.inl v) ↔ d.Cofacial u v := by
  simp only [Cofacial, support_subdivide]; rfl

@[simp] theorem outerCofacial_subdivide_iff (d : PlaneDrawing G) (u v : V) :
    d.subdivide.OuterCofacial (Sum.inl u) (Sum.inl v) ↔ d.OuterCofacial u v := by
  simp only [OuterCofacial, support_subdivide]; rfl

end PlaneDrawing

theorem Planar.subdivide {V E : Type*} {G : MultiGraph V E} (h : G.Planar) :
    G.subdivide.Planar := h.map PlaneDrawing.subdivide

end MultiGraph

namespace TwoTerminal
/-- The paper's outer-face condition, expressed using actual complementary faces
of an ordinary plane drawing of the incidence multigraph. -/
def PlanarEdgeGadget {W E : Type*} (G : TwoTerminal W E) : Prop :=
  ∃ d : MultiGraph.PlaneDrawing G, d.OuterCofacial (Sum.inl false) (Sum.inl true)

theorem PlanarEdgeGadget.planar {W E : Type*} {G : TwoTerminal W E}
    (h : PlanarEdgeGadget G) : MultiGraph.Planar G := by
  obtain ⟨d, _⟩ := h
  exact ⟨d⟩
end TwoTerminal
end PlanarHom

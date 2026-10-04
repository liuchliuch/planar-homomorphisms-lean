import PlanarHom.PlanarEmbedding

/-!
# Explicit geometric edge neighborhoods and insertion

A `RibbonDrawing` supplies continuous pinched rectangular neighborhoods of the
individual edge occurrences, disjoint away from the existing vertices. It implies
an ordinary `PlaneDrawing`; it is not an uninterpreted planarity predicate.

`thickenDrawing` and `insertDrawing` actually construct curves in these
neighborhoods. Their assumptions contain no planarity-preservation conclusion.
The general topological theorem constructing such ribbons from finite plane
drawings is established separately in `PlanarRibbonExistence`.
-/

noncomputable section
open Set unitInterval

namespace PlanarHom
namespace MultiGraph

/-- A separate pinched closed ribbon for each edge occurrence. Each endpoint
side collapses to its incident vertex; this permits loops without collapsing
any point of an edge interior. -/
structure RibbonDrawing {V E : Type*} (G : MultiGraph V E) where
  point : V → Plane
  point_injective : Function.Injective point
  band : E → C(I × I, Plane)
  band_zero : ∀ e y, band e (0,y) = point (G.src e)
  band_one : ∀ e y, band e (1,y) = point (G.dst e)
  band_injective : ∀ e f p q, Inside p.1 → Inside q.1 →
    band e p = band f q → e = f ∧ p = q
  band_avoids : ∀ e p, Inside p.1 → ∀ v, band e p ≠ point v

namespace RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A constant-height longitudinal curve in a ribbon. -/
def slice (y : I) : C(I, I × I) where
  toFun t := (t,y)
  continuous_toFun := by fun_prop

/-- Ribbons give ordinary, crossing-free edge curves. -/
def toPlaneDrawing (d : RibbonDrawing G) : PlaneDrawing G where
  point := d.point
  point_injective := d.point_injective
  curve e := (d.band e).comp (slice 0)
  curve_zero e := d.band_zero e 0
  curve_one e := d.band_one e 0
  interior_injective := by
    intro e f s t hs ht h
    obtain ⟨hef,hst⟩ := d.band_injective e f (s,0) (t,0) hs ht h
    exact ⟨hef, congrArg Prod.fst hst⟩
  interior_avoids e t ht v := d.band_avoids e (t,0) ht v

theorem planar (d : RibbonDrawing G) : G.Planar := ⟨d.toPlaneDrawing⟩

/-- Distinct, explicitly specified ribbon heights for finitely many copies. -/
def level {n : ℕ} (k : Fin n) : I :=
  ⟨((k : ℕ) : ℝ) / (n : ℝ), by
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
    exact ⟨div_nonneg (Nat.cast_nonneg _) hn.le,
      (div_le_one hn).mpr (by exact_mod_cast k.isLt.le)⟩⟩

theorem level_injective {n : ℕ} : Function.Injective (@level n) := by
  intro k l h
  have hn : (n : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Nat.zero_lt_of_lt k.isLt))
  have hh := congrArg (fun t : I => (t : ℝ)) h
  dsimp [level] at hh
  apply Fin.ext
  exact_mod_cast (div_left_inj' hn).mp hh

end RibbonDrawing

/-- Parallel thickening retains edge occurrences and original vertex labels. -/
def thicken {V E : Type*} (G : MultiGraph V E) (n : ℕ) : MultiGraph V (E × Fin n) where
  src p := G.src p.1
  dst p := G.dst p.1

namespace RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Explicit disjoint parallel curves, also when the original occurrence is a
loop. The case `n = 0` retains all isolated vertices and removes every edge. -/
def thickenDrawing (d : RibbonDrawing G) (n : ℕ) : PlaneDrawing (G.thicken n) where
  point := d.point
  point_injective := d.point_injective
  curve p := (d.band p.1).comp (slice (level p.2))
  curve_zero p := d.band_zero p.1 _
  curve_one p := d.band_one p.1 _
  interior_injective := by
    rintro ⟨e,k⟩ ⟨f,l⟩ s t hs ht h
    obtain ⟨hef,hst⟩ := d.band_injective e f (s,level k) (t,level l) hs ht h
    exact ⟨Prod.ext hef (level_injective (congrArg Prod.snd hst)),
      congrArg Prod.fst hst⟩
  interior_avoids p t ht v := d.band_avoids p.1 (t,level p.2) ht v

theorem thicken_planar (d : RibbonDrawing G) (n : ℕ) : (G.thicken n).Planar :=
  ⟨d.thickenDrawing n⟩

end RibbonDrawing
end MultiGraph

namespace TwoTerminal
open MultiGraph

/-- An explicitly drawn gadget in a unit square. Terminals are the lower left
and lower right corners. Every internal vertex and every edge interior has
strictly interior first coordinate; this is the precise region used by insertion.
The injectivity and avoidance fields are the actual geometric conditions. -/
structure StripDrawing {W F : Type*} (K : TwoTerminal W F) where
  point : Bool ⊕ W → I × I
  point_injective : Function.Injective point
  left : point (Sum.inl false) = (0,0)
  right : point (Sum.inl true) = (1,0)
  internal_inside : ∀ w, Inside (point (Sum.inr w)).1
  curve : F → C(I, I × I)
  curve_zero : ∀ f, curve f 0 = point (K.src f)
  curve_one : ∀ f, curve f 1 = point (K.dst f)
  curve_inside : ∀ f t, Inside t → Inside (curve f t).1
  interior_injective : ∀ e f s t, Inside s → Inside t →
    curve e s = curve f t → e = f ∧ s = t
  interior_avoids : ∀ e t, Inside t → ∀ v, curve e t ≠ point v

namespace StripDrawing
variable {W F : Type*} {K : TwoTerminal W F}

/-- Inclusion of the closed coordinate square into the actual plane. -/
def squareInPlane : C(I × I, Plane) where
  toFun p := ((p.1 : ℝ), (p.2 : ℝ))
  continuous_toFun := by fun_prop

theorem squareInPlane_injective : Function.Injective squareInPlane := by
  intro p q h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- These certificates give actual ordinary plane drawings, not just rotation
or Euler data. -/
def toPlaneDrawing (k : StripDrawing K) : PlaneDrawing K where
  point v := squareInPlane (k.point v)
  point_injective := squareInPlane_injective.comp k.point_injective
  curve f := squareInPlane.comp (k.curve f)
  curve_zero f := congrArg squareInPlane (k.curve_zero f)
  curve_one f := congrArg squareInPlane (k.curve_one f)
  interior_injective e f s t hs ht h :=
    k.interior_injective e f s t hs ht (squareInPlane_injective h)
  interior_avoids e t ht v h :=
    k.interior_avoids e t ht v (squareInPlane_injective h)

theorem planar (k : StripDrawing K) : MultiGraph.Planar K := ⟨k.toPlaneDrawing⟩

/-- The straight terminal-to-terminal segment. -/
def singleEdge : StripDrawing TwoTerminal.singleEdge where
  point := Sum.elim (fun b => if b then (1,0) else (0,0)) Empty.elim
  point_injective := by
    rintro (a | a) (b | b) h
    · cases a <;> cases b <;> simp_all
    · exact b.elim
    · exact a.elim
    · exact a.elim
  left := rfl
  right := rfl
  internal_inside w := w.elim
  curve _ := RibbonDrawing.slice 0
  curve_zero _ := rfl
  curve_one _ := rfl
  curve_inside _ t ht := ht
  interior_injective e f s t hs ht h := ⟨Subsingleton.elim _ _, congrArg Prod.fst h⟩
  interior_avoids := by
    rintro e t ht (b | w) h
    · have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
      cases b <;> dsimp [RibbonDrawing.slice] at hx <;> rcases ht with ⟨h0,h1⟩ <;> linarith
    · exact w.elim

end StripDrawing
end TwoTerminal

namespace MultiGraph

/-- Include one gadget's vertices, identifying its two terminals with the
chosen host edge's endpoints. On a loop, both terminals become the same vertex. -/
def insertVertex {V E W : Type*} (G : MultiGraph V E) (e : E) :
    Bool ⊕ W → V ⊕ (E × W)
  | Sum.inl false => Sum.inl (G.src e)
  | Sum.inl true => Sum.inl (G.dst e)
  | Sum.inr w => Sum.inr (e,w)

/-- Replace every host edge occurrence by a separate copy of the gadget,
retaining each gadget edge occurrence and all old isolated vertices. -/
def insert {V E W F : Type*} (G : MultiGraph V E) (K : TwoTerminal W F) :
    MultiGraph (V ⊕ (E × W)) (E × F) where
  src p := G.insertVertex p.1 (K.src p.2)
  dst p := G.insertVertex p.1 (K.dst p.2)

namespace RibbonDrawing
variable {V E W F : Type*} {G : MultiGraph V E} {K : TwoTerminal W F}

/-- The actual vertex placement after insertion. -/
def insertPoint (d : RibbonDrawing G) (k : TwoTerminal.StripDrawing K) :
    V ⊕ (E × W) → Plane :=
  Sum.elim d.point (fun p => d.band p.1 (k.point (Sum.inr p.2)))

theorem insertPoint_attach (d : RibbonDrawing G) (k : TwoTerminal.StripDrawing K)
    (e : E) (v : Bool ⊕ W) :
    d.insertPoint k (G.insertVertex e v) = d.band e (k.point v) := by
  rcases v with (b | w)
  · cases b
    · simp [insertPoint, insertVertex, k.left, d.band_zero]
    · simp [insertPoint, insertVertex, k.right, d.band_one]
  · rfl

/-- Explicit geometric gadget replacement inside pairwise disjoint edge
neighborhoods. No condition asserts the desired planarity conclusion. -/
def insertDrawing (d : RibbonDrawing G) (k : TwoTerminal.StripDrawing K) :
    PlaneDrawing (G.insert K) where
  point := d.insertPoint k
  point_injective := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (d.point_injective h)
      | inr q => exact False.elim (d.band_avoids q.1 _ (k.internal_inside q.2) v h.symm)
    | inr p =>
      cases y with
      | inl w => exact False.elim (d.band_avoids p.1 _ (k.internal_inside p.2) w h)
      | inr q =>
        obtain ⟨he,hv⟩ := d.band_injective p.1 q.1 _ _
          (k.internal_inside p.2) (k.internal_inside q.2) h
        have hw : p.2 = q.2 := Sum.inr.inj (k.point_injective hv)
        exact congrArg Sum.inr (Prod.ext he hw)
  curve p := (d.band p.1).comp (k.curve p.2)
  curve_zero p := by
    change d.band p.1 (k.curve p.2 0) = d.insertPoint k _
    rw [k.curve_zero, insert, d.insertPoint_attach]
  curve_one p := by
    change d.band p.1 (k.curve p.2 1) = d.insertPoint k _
    rw [k.curve_one, insert, d.insertPoint_attach]
  interior_injective := by
    rintro ⟨e,a⟩ ⟨f,b⟩ s t hs ht h
    obtain ⟨hef,hab⟩ := d.band_injective e f _ _
      (k.curve_inside a s hs) (k.curve_inside b t ht) h
    obtain ⟨hab,hst⟩ := k.interior_injective a b s t hs ht hab
    exact ⟨Prod.ext hef hab,hst⟩
  interior_avoids := by
    rintro ⟨e,a⟩ t ht (v | p) h
    · exact d.band_avoids e _ (k.curve_inside a t ht) v h
    · have hq := (d.band_injective e p.1 _ _
        (k.curve_inside a t ht) (k.internal_inside p.2) h).2
      exact k.interior_avoids a t ht (Sum.inr p.2) hq

theorem insert_planar (d : RibbonDrawing G) (k : TwoTerminal.StripDrawing K) :
    (G.insert K).Planar := ⟨d.insertDrawing k⟩

end RibbonDrawing
end MultiGraph
end PlanarHom

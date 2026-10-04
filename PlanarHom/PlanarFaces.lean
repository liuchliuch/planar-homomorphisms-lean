import PlanarHom.PlanarRibbons
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.Order.Bornology

/-!
# Actual outer-face certificates for explicit gadgets

For a drawing contained in the closed upper half-plane, all vertices on the
horizontal axis border the same unbounded complementary component. This theorem
turns the geometric square certificates used by insertion into the paper's actual
outer-face gadget condition; it is not just an informal drawing convention.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom
namespace MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A direct outer-face criterion proved from an unbounded connected subset of
the actual drawing complement. -/
theorem outerCofacial_of_upperHalfPlane (d : PlaneDrawing G)
    (hs : ∀ p ∈ d.support, 0 ≤ p.2) (u v : V)
    (hu : (d.point u).2 = 0) (hv : (d.point v).2 = 0) : d.OuterCofacial u v := by
  let lower : Set Plane := Set.univ ×ˢ Set.Iio 0
  have hlower : lower ⊆ d.supportᶜ := by
    intro p hp hmem
    have hp' : p.2 < 0 := hp.2
    linarith [hs p hmem]
  have hz : ((0,-1) : Plane) ∈ lower := by simp [lower]
  have hconn : IsPreconnected lower := isPreconnected_univ.prod isPreconnected_Iio
  have hsub := hconn.subset_connectedComponentIn hz hlower
  refine ⟨(0,-1), hlower hz, ?_, ?_, ?_⟩
  · intro hb
    have hbLower := hb.subset hsub
    have hbIio : Bornology.IsBounded (Set.Iio (0 : ℝ)) :=
      hbLower.snd_of_prod Set.univ_nonempty
    exact (not_bddBelow_Iio (a := (0 : ℝ))) hbIio.bddBelow
  · apply closure_mono hsub
    simp [lower, closure_prod_eq, closure_Iio, hu]
  · apply closure_mono hsub
    simp [lower, closure_prod_eq, closure_Iio, hv]

end MultiGraph.PlaneDrawing

namespace TwoTerminal.StripDrawing
open MultiGraph
variable {W F : Type*} {K : TwoTerminal W F}

/-- Every strip certificate satisfies the original outer-face definition, not
merely abstract planarity. -/
theorem outerCofacial (k : StripDrawing K) :
    k.toPlaneDrawing.OuterCofacial (Sum.inl false) (Sum.inl true) := by
  apply k.toPlaneDrawing.outerCofacial_of_upperHalfPlane
  · intro p hp
    rcases hp with (⟨v,rfl⟩ | hp)
    · exact (k.point v).2.2.1
    · simp only [Set.mem_iUnion, Set.mem_range] at hp
      obtain ⟨f,t,rfl⟩ := hp
      exact (k.curve f t).2.2.1
  · simp [toPlaneDrawing, squareInPlane, k.left]
  · simp [toPlaneDrawing, squareInPlane, k.right]

theorem planarEdgeGadget (k : StripDrawing K) : TwoTerminal.PlanarEdgeGadget K :=
  ⟨k.toPlaneDrawing, k.outerCofacial⟩

/-- Explicit bowed arcs, all lying above the terminal-to-terminal segment. -/
def bowCurve {n : ℕ} (e : Fin n) : C(I, I × I) where
  toFun t := (t, RibbonDrawing.level e * t * unitInterval.symm t)
  continuous_toFun := by
    apply continuous_id.prodMk
    apply Continuous.subtype_mk
    change Continuous (fun t : I => (RibbonDrawing.level e : ℝ) * (t : ℝ) * (1 - (t : ℝ)))
    fun_prop

@[simp] theorem bowCurve_zero {n : ℕ} (e : Fin n) : bowCurve e 0 = (0,0) := by
  ext <;> simp [bowCurve, unitInterval.symm]

@[simp] theorem bowCurve_one {n : ℕ} (e : Fin n) : bowCurve e 1 = (1,0) := by
  ext <;> simp [bowCurve, unitInterval.symm]

theorem bowCurve_interior_injective {n : ℕ} (e f : Fin n) (s t : I)
    (hs : Inside s) (ht : Inside t) (h : bowCurve e s = bowCurve f t) :
    e = f ∧ s = t := by
  have hst : s = t := congrArg Prod.fst h
  subst t
  refine ⟨?_, rfl⟩
  have hy := congrArg (fun p : I × I => (p.2 : ℝ)) h
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hs.1
  have hs1 : 1 - (s : ℝ) ≠ 0 := ne_of_gt (by linarith [hs.2])
  dsimp [bowCurve, unitInterval.symm] at hy
  apply RibbonDrawing.level_injective
  apply Subtype.ext
  exact mul_right_cancel₀ hs0 (mul_right_cancel₀ hs1 hy)

/-- A proved outer-face drawing of every finite parallel-edge gadget, including
the zero-edge case with both isolated terminal vertices retained. -/
def parallelEdges (n : ℕ) : StripDrawing (TwoTerminal.parallelEdges n) where
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
  curve := bowCurve
  curve_zero := bowCurve_zero
  curve_one := bowCurve_one
  curve_inside _ t ht := ht
  interior_injective := bowCurve_interior_injective
  interior_avoids := by
    rintro e t ht (b | w) h
    · have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
      cases b <;> dsimp [bowCurve] at hx <;> rcases ht with ⟨h0,h1⟩ <;> linarith
    · exact w.elim

theorem parallelEdges_planarEdgeGadget (n : ℕ) :
    TwoTerminal.PlanarEdgeGadget (TwoTerminal.parallelEdges n) :=
  (parallelEdges n).planarEdgeGadget

theorem singleEdge_planarEdgeGadget :
    TwoTerminal.PlanarEdgeGadget TwoTerminal.singleEdge := singleEdge.planarEdgeGadget

end TwoTerminal.StripDrawing
end PlanarHom

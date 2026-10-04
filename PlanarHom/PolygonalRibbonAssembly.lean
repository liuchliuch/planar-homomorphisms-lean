import PlanarHom.PolygonalUniformWidth
import PlanarHom.PlanarRibbons
import PlanarHom.PolygonalDrawingIncidence

/-!
# Assemble actual polygonal ribbons from the proved local strip inequalities

The global band is the explicitly continuous interpolation of the original and
vertex-shifted polygonal paths. The common finite width properties recover the
original center points, after which the ordinary drawing axioms recover edge and
longitudinal parameters. Self-strip equality recovers transverse parameters.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.Polygonal.Chain
open MultiGraph
variable {U : Set Plane} {x y : Plane}

/-- A simultaneous segment representation independent of the transverse height. -/
theorem vertexBand_offset_joint_strip (p : PlanarHom.Polygonal.Chain U x y)
    (hn : p.length ≠ 0) (N : Plane → Plane) (ε : ℝ) (t : I) :
    ∃ a b, (a,b) ∈ p.segments ∧ ∃ u : I,
      p.strictPath t = AffineMap.lineMap a b (u : ℝ) ∧
      ∀ s : I, p.vertexBand (fun v => v + ε • N v) (t,s) =
        stripMap a b (ε • N a) (ε • N b) (u,s) := by
  obtain ⟨a,b,hab,u,hu,hfu⟩ := p.strictPath_joint_segment hn (fun v => v + ε • N v) t
  refine ⟨a,b,hab,u,hu,?_⟩
  intro s
  change p.strictPath t + (s : ℝ) •
    ((p.mapVertices (fun v => v + ε • N v)).strictPath t - p.strictPath t) = _
  rw [hu,hfu]
  apply Prod.ext <;> simp [stripMap,strip,AffineMap.lineMap_apply_module] <;> ring

end PlanarHom.Polygonal.Chain

namespace PlanarHom.MultiGraph.PolygonalDrawing
open PlanarHom.Polygonal
variable {V E : Type*} {G : MultiGraph V E}

/-- The explicitly drawn ribbon, constructed from the actual numerical width
proved for its finite segment geometry. The final existence theorem supplies
these local data from ordinary planarity. -/
def ribbonOfGoodWidth (d : PolygonalDrawing G) (S : Finset (Plane × Plane))
    (hS : ∀ e p, p ∈ (d.chain e).segments → p ∈ S)
    (N : Plane → Plane) (ε : ℝ) (hzero : ∀ x ∈ d.hostSet, N x = 0)
    (hgood : GoodStripWidth S d.hostSet N ε) : RibbonDrawing G where
  point := d.drawing.point
  point_injective := d.drawing.point_injective
  band e := (d.chain e).vertexBand (fun v => v + ε • N v)
  band_zero e s := by
    apply Polygonal.Chain.vertexBand_source
    simp [hzero _ ⟨G.src e,rfl⟩]
  band_one e s := by
    apply Polygonal.Chain.vertexBand_target
    simp [hzero _ ⟨G.dst e,rfl⟩]
  band_injective := by
    rintro e f ⟨t,s⟩ ⟨u,v⟩ ht hu heq
    obtain ⟨a,b,hab,l,hl,hband⟩ := (d.chain e).vertexBand_offset_joint_strip
      (d.chain_length_ne_zero e) N ε t
    obtain ⟨c,k,hck,m,hm,hband'⟩ := (d.chain f).vertexBand_offset_joint_strip
      (d.chain_length_ne_zero f) N ε u
    have he : (a,b) ∈ S := hS e (a,b) hab
    have hf : (c,k) ∈ S := hS f (c,k) hck
    have hc := hgood.2.1 (a,b) he (c,k) hf (l,s) (m,v)
      ((hband s).symm.trans (heq.trans (hband' v)))
    have horig : d.drawing.curve e t = d.drawing.curve f u := by
      rw [d.curve_eq,d.curve_eq]
      exact hl.trans (hc.trans hm.symm)
    obtain ⟨hef,htu⟩ := d.drawing.interior_injective e f t u ht hu horig
    subst f
    subst u
    have hsame := hgood.1 (a,b) he (l,s) (l,v)
      ((hband s).symm.trans (heq.trans (hband v)))
    rcases hsame with hpq | ⟨hhost,h0,_⟩ | ⟨hhost,h1,_⟩
    · have hsv : s = v := congrArg (fun p : I × I => p.2) hpq
      cases hsv
      exact ⟨rfl,rfl⟩
    · change l = 0 at h0
      obtain ⟨w,hw⟩ := hhost
      have hcenter : d.drawing.curve e t = d.drawing.point w := by
        rw [d.curve_eq]
        exact hl.trans ((by simp [h0] : AffineMap.lineMap a b (l : ℝ) = a).trans hw.symm)
      exact (d.drawing.interior_avoids e t ht w hcenter).elim
    · change l = 1 at h1
      obtain ⟨w,hw⟩ := hhost
      have hcenter : d.drawing.curve e t = d.drawing.point w := by
        rw [d.curve_eq]
        exact hl.trans ((by simp [h1] : AffineMap.lineMap a b (l : ℝ) = b).trans hw.symm)
      exact (d.drawing.interior_avoids e t ht w hcenter).elim
  band_avoids := by
    rintro e ⟨t,s⟩ ht w heq
    obtain ⟨a,b,hab,l,hl,hband⟩ := (d.chain e).vertexBand_offset_joint_strip
      (d.chain_length_ne_zero e) N ε t
    have hc := hgood.2.2 (a,b) (hS e (a,b) hab) (d.drawing.point w) ⟨w,rfl⟩ (l,s)
      ((hband s).symm.trans heq)
    apply d.drawing.interior_avoids e t ht w
    rw [d.curve_eq]
    exact hl.trans hc

end PlanarHom.MultiGraph.PolygonalDrawing

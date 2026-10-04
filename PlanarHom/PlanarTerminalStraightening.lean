import PlanarHom.PlanarLocalizedSegmentCollapse
import PlanarHom.PolygonalArcCollapse
import PlanarHom.PlanarCofacialPolygonalization
import PlanarHom.PolygonalFaceAccess

/-!
# Straight terminal access from ordinary cofaciality

A simple external polygonal arc is reduced by finitely many explicit localized
segment collapses. Each collapse is injective on the retained drawing and keeps
the remaining polygonal suffix unchanged as a set. The final segment therefore
meets the transformed graph only at the two terminal vertices.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A true external polygonal arc can be made straight by a continuous map
injective on the complete retained drawing. -/
theorem exists_straightTerminalDrawing_of_external_chain (d : PlaneDrawing G)
    {u v : V} (huv : u ≠ v)
    (p : Polygonal.Chain Set.univ (d.point u) (d.point v)) (hp : p.IsSimple)
    (havoid : ∀ t, Inside t → p.strictPath t ∉ d.support) :
    ∃ D : PlaneDrawing G, ∀ w, w ∈ [D.point u -[ℝ] D.point v] →
      w ∈ D.support → w = D.point u ∨ w = D.point v := by
  have hcontact : ∀ w, w ∈ p.support → w ∈ d.support →
      w = d.point u ∨ w = d.point v := by
    intro w hw hS
    rw [← Polygonal.Chain.range_strictPath] at hw
    obtain ⟨t,rfl⟩ := hw
    by_cases h0 : t = 0
    · left
      simpa [h0] using p.strictPath.source
    by_cases h1 : t = 1
    · right
      simpa [h1] using p.strictPath.target
    exact (havoid t (inside_of_ne_endpoints h0 h1) hS).elim
  obtain ⟨F,c,hFinj,hFu,hFv,_,hfinal⟩ :=
    p.exists_straight_segment_of_collapse
      (fun hab _ hK hdis => exists_localizedSegmentCollapse hab hK hdis)
      hp (d.point_injective.ne huv) d.support hcontact
  let D := d.mapOnSupport F hFinj
  refine ⟨D,?_⟩
  intro w hw hS
  change w = F (d.point u) ∨ w = F (d.point v)
  change w ∈ [F (d.point u) -[ℝ] F (d.point v)] at hw
  rw [hFu,hFv] at hw ⊢
  apply hfinal w hw
  rwa [support_mapOnSupport] at hS

/-- Distinct terminals cofacial in the original ordinary drawing admit a new
ordinary drawing with an actual straight external terminal segment. -/
theorem Cofacial.exists_straightTerminalDrawing [Finite V] [Finite E]
    {d : PlaneDrawing G} {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) :
    ∃ D : PlaneDrawing G, ∀ w, w ∈ [D.point u -[ℝ] D.point v] →
      w ∈ D.support → w = D.point u ∨ w = D.point v := by
  obtain ⟨P,hP⟩ := hface.exists_cofacialPolygonalDrawing huv
  obtain ⟨p,hp,havoid⟩ := P.exists_external_arc hP huv
  exact P.drawing.exists_straightTerminalDrawing_of_external_chain huv p hp havoid

end PlanarHom.MultiGraph.PlaneDrawing

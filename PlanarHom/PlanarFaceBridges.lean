import PlanarHom.PlanarNeighborhoods
import PlanarHom.PolygonalAttachments
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Polygonal bridges approaching vertices of an actual complementary face

Closure incidence with a complementary face yields simple polygonal arcs whose
endpoints lie on the drawing arbitrarily near the prescribed vertices. Their
open interiors avoid the entire drawing. The endpoints need not yet be the
vertices themselves: identifying the short incident tails is a separate
contraction obligation, not an assumed boundary-accessibility theorem.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

private theorem plane_locallyConnected : LocallyConnectedSpace Plane :=
  locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr (by
    intro x U hU
    obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
    exact ⟨Metric.ball x ε,hsub,Metric.isOpen_ball,Metric.mem_ball_self hε,
      (convex_ball x ε).isConnected ⟨x,Metric.mem_ball_self hε⟩⟩)

/-- The actual face is open and polygonally connected. -/
theorem face_polygonallyConnected [Finite V] [Finite E] (d : PlaneDrawing G)
    {z : Plane} (hz : z ∉ d.support) {x y : Plane}
    (hx : x ∈ connectedComponentIn d.supportᶜ z)
    (hy : y ∈ connectedComponentIn d.supportᶜ z) :
    Polygonal.Joined (connectedComponentIn d.supportᶜ z) x y := by
  letI := plane_locallyConnected
  exact Polygonal.joined_of_isOpen_isPreconnected
    (d.isCompact_support.isClosed.isOpen_compl.connectedComponentIn)
    (isConnected_connectedComponentIn_iff.mpr hz).isPreconnected hx hy

/-- A genuine finite simple polygonal arc, with only its endpoints on the graph. -/
structure NearFaceBridge (d : PlaneDrawing G) (u v : V) (ε : ℝ) where
  left : Plane
  right : Plane
  left_mem : left ∈ d.support
  right_mem : right ∈ d.support
  left_near : dist left (d.point u) < ε
  right_near : dist right (d.point v) < ε
  distinct : left ≠ right
  chain : Polygonal.Chain Set.univ left right
  simple : chain.IsSimple
  avoids : ∀ t : I, Inside t → chain.strictPath t ∉ d.support

/-- Mere closure incidence suffices for arbitrarily close, actual polygonal
bridges. This does not replace their near-vertex endpoints by the vertices. -/
theorem Cofacial.exists_nearFaceBridge [Finite V] [Finite E] {d : PlaneDrawing G}
    {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (d.NearFaceBridge u v ε) := by
  obtain ⟨z,hz,hu,hv⟩ := hface
  let δ := min ε (dist (d.point u) (d.point v) / 3)
  have hsep : 0 < dist (d.point u) (d.point v) :=
    dist_pos.mpr (d.point_injective.ne huv)
  have hδ : 0 < δ := lt_min hε (by positivity)
  obtain ⟨x,hx,hxu⟩ := Metric.mem_closure_iff.mp hu δ hδ
  obtain ⟨y,hy,hyv⟩ := Metric.mem_closure_iff.mp hv δ hδ
  have hxnot : x ∉ d.support := connectedComponentIn_subset _ _ hx
  have hynot : y ∉ d.support := connectedComponentIn_subset _ _ hy
  obtain ⟨a,ha,hxa,haSeg,haOnly⟩ := Polygonal.exists_first_contact
    d.isCompact_support hxnot (Or.inl ⟨u,rfl⟩ : d.point u ∈ d.support)
  obtain ⟨b,hb,hyb,hbSeg,hbOnly⟩ := Polygonal.exists_first_contact
    d.isCompact_support hynot (Or.inl ⟨v,rfl⟩ : d.point v ∈ d.support)
  have hballx : [x -[ℝ] d.point u] ⊆ Metric.ball (d.point u) δ :=
    (convex_ball _ _).segment_subset (by simpa only [Metric.mem_ball,dist_comm] using hxu)
      (Metric.mem_ball_self hδ)
  have hbally : [y -[ℝ] d.point v] ⊆ Metric.ball (d.point v) δ :=
    (convex_ball _ _).segment_subset (by simpa only [Metric.mem_ball,dist_comm] using hyv)
      (Metric.mem_ball_self hδ)
  have hau : dist a (d.point u) < δ := hballx (haSeg (right_mem_segment ℝ _ _))
  have hbv : dist b (d.point v) < δ := hbally (hbSeg (right_mem_segment ℝ _ _))
  have hab : a ≠ b := by
    intro hab
    have htri := dist_triangle (d.point u) a (d.point v)
    have hδle : δ ≤ dist (d.point u) (d.point v) / 3 := min_le_right _ _
    rw [← hab] at hbv
    rw [dist_comm (d.point u) a] at htri
    linarith
  obtain ⟨p⟩ := d.face_polygonallyConnected hz hx hy
  let l : Polygonal.Chain Set.univ a x := .segment (subset_univ _)
  let m : Polygonal.Chain Set.univ x y := p.mono (subset_univ _)
  let r : Polygonal.Chain Set.univ y b := .segment (subset_univ _)
  have hl : l.support = [x -[ℝ] a] := by
    rw [← Polygonal.Chain.range_strictPath]
    change Set.range (Path.segment a x) = _
    rw [Path.range_segment,segment_symm]
  have hr : r.support = [y -[ℝ] b] := by
    rw [← Polygonal.Chain.range_strictPath]
    exact Path.range_segment _ _
  have hm : m.support ⊆ d.supportᶜ :=
    (show m.support = p.support from p.support_mono _).subset.trans
      (p.support_subset.trans (connectedComponentIn_subset _ _))
  obtain ⟨q,hq,hqsub⟩ := ((l.append m).append r).exists_simple
  have hqOnly (w : Plane) (hw : w ∈ q.support) (hwG : w ∈ d.support) : w = a ∨ w = b := by
    have hh := hqsub hw
    rw [Polygonal.Chain.support_append,Polygonal.Chain.support_append,hl,hr] at hh
    rcases hh with (hh | hh) | hh
    · exact Or.inl (haOnly w hh hwG)
    · exact (hm hh hwG).elim
    · exact Or.inr (hbOnly w hh hwG)
  refine ⟨⟨a,b,ha,hb,hau.trans_le (min_le_left _ _),hbv.trans_le (min_le_left _ _),
    hab,q,hq,?_⟩⟩
  intro t ht hmem
  have hinj := q.strictPath_injective hq hab
  have hqt : q.strictPath t ∈ q.support := by
    rw [← Polygonal.Chain.range_strictPath]
    exact ⟨t,rfl⟩
  rcases hqOnly _ hqt hmem with h | h
  · have ht0 := hinj (h.trans q.strictPath.source.symm)
    simp [Inside,ht0] at ht
  · have ht1 := hinj (h.trans q.strictPath.target.symm)
    simp [Inside,ht1] at ht

/-- A point of the drawing outside the forbidden pieces is either the chosen
vertex or lies strictly in an incident first/last third. This includes loops. -/
theorem support_not_forbidden_incident (d : PlaneDrawing G) (v : V) {x : Plane}
    (hx : x ∈ d.support) (hnot : x ∉ d.forbidden v) :
    x = d.point v ∨ ∃ e t, Inside t ∧ d.curve e t = x ∧
      ((G.src e = v ∧ t < firstThird) ∨ (G.dst e = v ∧ secondThird < t)) := by
  rcases hx with ⟨w,rfl⟩ | hx
  · left
    by_contra hw
    exact hnot (Or.inl ⟨w,fun h => hw (congrArg d.point h),rfl⟩)
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hx
    by_cases h0 : t = 0
    · left
      rw [h0,d.curve_zero]
      by_contra he
      exact hnot (Or.inl ⟨G.src e,fun h => he (congrArg d.point h),by rw [h0,d.curve_zero]⟩)
    by_cases h1 : t = 1
    · left
      rw [h1,d.curve_one]
      by_contra he
      exact hnot (Or.inl ⟨G.dst e,fun h => he (congrArg d.point h),by rw [h1,d.curve_one]⟩)
    right
    refine ⟨e,t,inside_of_ne_endpoints h0 h1,rfl,?_⟩
    have hnotIcc : ¬ (portLo G v e ≤ t ∧ t ≤ portHi G v e) := by
      intro ht
      exact hnot (Or.inr (Set.mem_iUnion.mpr ⟨e,t,ht,rfl⟩))
    by_cases hs : G.src e = v
    · by_cases ht : t < firstThird
      · exact Or.inl ⟨hs,ht⟩
      · right
        have hlo : portLo G v e ≤ t := by simpa [portLo,hs] using le_of_not_gt ht
        have hhi : portHi G v e < t := lt_of_not_ge (fun h => hnotIcc ⟨hlo,h⟩)
        by_cases hd : G.dst e = v
        · exact ⟨hd,by simpa [portHi,hd] using hhi⟩
        · have ht : (1 : I) < t := by simpa [portHi,hd] using hhi
          exact (not_lt_of_ge (show t ≤ (1 : I) from le_top) ht).elim
    · have hlo : portLo G v e ≤ t := by simp [portLo,hs]
      have hhi : portHi G v e < t := lt_of_not_ge (fun h => hnotIcc ⟨hlo,h⟩)
      right
      by_cases hd : G.dst e = v
      · exact ⟨hd,by simpa [portHi,hd] using hhi⟩
      · have ht : (1 : I) < t := by simpa [portHi,hd] using hhi
        exact (not_lt_of_ge (show t ≤ (1 : I) from le_top) ht).elim

/-- Close enough contacts are on the correct actual incidence tails. -/
theorem NearFaceBridge.incident_contacts {d : PlaneDrawing G} {u v : V} {r : ℝ}
    (B : d.NearFaceBridge u v r) (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) :
    (B.left = d.point u ∨ ∃ e t, Inside t ∧ d.curve e t = B.left ∧
      ((G.src e = u ∧ t < firstThird) ∨ (G.dst e = u ∧ secondThird < t))) ∧
    (B.right = d.point v ∨ ∃ e t, Inside t ∧ d.curve e t = B.right ∧
      ((G.src e = v ∧ t < firstThird) ∨ (G.dst e = v ∧ secondThird < t))) := by
  constructor
  · exact d.support_not_forbidden_incident u B.left_mem (by
      intro h
      have := hr u _ h
      linarith [B.left_near])
  · exact d.support_not_forbidden_incident v B.right_mem (by
      intro h
      have := hr v _ h
      linarith [B.right_near])

end PlanarHom.MultiGraph.PlaneDrawing

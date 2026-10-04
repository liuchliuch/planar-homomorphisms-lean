import PlanarHom.PolygonalFiniteIncidence
import PlanarHom.PlanarFaceBridges
import PlanarHom.PlanarEdgeOperations
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Actual boundary access in a finite polygonal drawing

Finite straight-piece geometry gives a radial access neighborhood at every
vertex. This is derived from the drawing, not supplied as a face-accessibility
certificate. Transfer of a prescribed ordinary face through polygonal redrawing
is a separate obligation.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph

/-- A short radial segment avoiding the longer ray endpoint cannot cross that
ray and then leave it. -/
theorem short_radial_intersection {c b q w : Plane} (hcb : c ≠ b)
    (hd : dist q c ≤ dist b c) (hq : q ∉ [c -[ℝ] b])
    (hwq : w ∈ [c -[ℝ] q]) (hwb : w ∈ [c -[ℝ] b]) : w = c := by
  rw [segment_eq_image_lineMap] at hwq hwb
  obtain ⟨s,hs,rfl⟩ := hwq
  obtain ⟨t,ht,heq⟩ := hwb
  by_cases hs0 : s = 0
  · simp [hs0]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hbc : 0 < dist b c := dist_pos.mpr hcb.symm
  have hdist := congrArg (fun x => dist x c) heq
  simp only [dist_lineMap_left,Real.norm_eq_abs,abs_of_nonneg hs.1,
    abs_of_nonneg ht.1,dist_comm c b,dist_comm c q] at hdist
  have hts : t ≤ s := by nlinarith
  have hvec : t • (b-c) = s • (q-c) := by
    calc
      t • (b-c) = AffineMap.lineMap c b t - c := by
        simp only [AffineMap.lineMap_apply_module]; module
      _ = AffineMap.lineMap c q s - c := congrArg (fun x => x-c) heq
      _ = s • (q-c) := by simp only [AffineMap.lineMap_apply_module]; module
  have hscale : (t/s) • (b-c) = q-c := by
    rw [div_eq_inv_mul,mul_smul,hvec,smul_smul,inv_mul_cancel₀ hs0,one_smul]
  apply False.elim
  apply hq
  rw [segment_eq_image_lineMap]
  refine ⟨t/s,⟨div_nonneg ht.1 hs.1,(div_le_one hspos).mpr hts⟩,?_⟩
  calc
    AffineMap.lineMap c b (t/s) = c + (t/s) • (b-c) := by
      simp only [AffineMap.lineMap_apply_module]; module
    _ = q := by rw [hscale]; abel

namespace PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Each actual piece has a positive radial-access radius at a host vertex. -/
theorem segment_access_radius (d : PolygonalDrawing G) (v : V)
    {a b : Plane} (hab : (a,b) ∈ d.segmentSet) :
    ∃ r : ℝ, 0 < r ∧ ∀ q, dist q (d.drawing.point v) < r → q ∉ [a -[ℝ] b] →
      ∀ w, w ∈ [d.drawing.point v -[ℝ] q] → w ∈ [a -[ℝ] b] → w = d.drawing.point v := by
  obtain ⟨e,he⟩ := hab
  have hne : a ≠ b := d.segment_ne ⟨e,he⟩
  by_cases ha : a = d.drawing.point v
  · subst a
    exact ⟨dist b (d.drawing.point v),dist_pos.mpr hne.symm,
      fun q hq hn w hw hwb => short_radial_intersection hne hq.le hn hw hwb⟩
  by_cases hb : b = d.drawing.point v
  · subst b
    refine ⟨dist a (d.drawing.point v),dist_pos.mpr hne,?_⟩
    intro q hq hn w hw hwa
    rw [segment_symm] at hn hwa
    exact short_radial_intersection hne.symm hq.le hn hw hwa
  have hc : d.drawing.point v ∉ [a -[ℝ] b] := by
    intro hc
    rcases d.host_segment_contact ⟨e,he⟩ ⟨v,rfl⟩ hc with ha' | hb'
    · exact ha ha'
    · exact hb hb'
  have hcompact : IsCompact [a -[ℝ] b] := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hclosed := hcompact.isClosed
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl _ hc
  refine ⟨r,hr,?_⟩
  intro q hq _ w hw hwa
  exact (hball ((convex_ball _ _).segment_subset (Metric.mem_ball_self hr) hq hw) hwa).elim

/-- A finite polygonal drawing has a genuine straight access neighborhood at
any vertex, including isolated vertices and vertices supporting loops. -/
theorem exists_access_radius [Finite V] [Finite E] (d : PolygonalDrawing G) (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ q, dist q (d.drawing.point v) < r → q ∉ d.drawing.support →
      ∀ w, w ∈ [d.drawing.point v -[ℝ] q] → w ∈ d.drawing.support → w = d.drawing.point v := by
  let A := {p : Plane × Plane // p ∈ d.segmentSet}
  letI : Finite A := d.finite_segmentSet.to_subtype
  have hlocal : ∀ p : A, ∃ r : ℝ, 0 < r ∧ ∀ q, dist q (d.drawing.point v) < r →
      q ∉ [p.1.1 -[ℝ] p.1.2] → ∀ w, w ∈ [d.drawing.point v -[ℝ] q] →
      w ∈ [p.1.1 -[ℝ] p.1.2] → w = d.drawing.point v :=
    fun p => d.segment_access_radius v p.2
  choose r hr haccess using hlocal
  obtain ⟨ρ,hρ,hρr⟩ := PlaneDrawing.finite_positive_lower_bound r hr
  obtain ⟨tau,htau,hsep⟩ := d.drawing.exists_vertex_radius
  refine ⟨min ρ tau,lt_min hρ htau,?_⟩
  intro q hq hn w hw hwG
  rcases hwG with ⟨z,rfl⟩ | hwG
  · by_cases hz : z = v
    · exact congrArg d.drawing.point hz
    · have hfar := d.drawing.radius_vertex_separation hsep hz
      have hnear : dist (d.drawing.point z) (d.drawing.point v) < min ρ tau :=
        (convex_ball _ _).segment_subset (Metric.mem_ball_self (lt_min hρ htau)) hq hw
      have hle : min ρ tau ≤ tau := min_le_right _ _
      exfalso
      linarith
  · obtain ⟨e,t,ht⟩ := Set.mem_iUnion.mp hwG
    obtain ⟨a,b,hab,s,hs,_⟩ := (d.chain e).strictPath_joint_segment
      (d.chain_length_ne_zero e) id t
    have hpair : (a,b) ∈ d.segmentSet := ⟨e,hab⟩
    apply haccess ⟨(a,b),hpair⟩ q (hq.trans_le ((min_le_left _ _).trans (hρr _)))
    · intro hqseg
      exact hn (d.chain_support_subset_drawing e ((d.chain e).segment_subset_support hab hqseg))
    · exact hw
    · rw [← ht,d.curve_eq]
      change (d.chain e).strictPath t ∈ [a -[ℝ] b]
      rw [hs,segment_eq_image_lineMap]
      exact ⟨(s : ℝ),s.2,rfl⟩

/-- For an actual polygonal drawing, cofacial distinct vertices admit a genuine
simple polygonal connecting arc in the complement, with precisely those endpoints. -/
theorem exists_external_arc [Finite V] [Finite E] (d : PolygonalDrawing G)
    {u v : V} (hface : d.drawing.Cofacial u v) (huv : u ≠ v) :
    ∃ p : Polygonal.Chain Set.univ (d.drawing.point u) (d.drawing.point v),
      p.IsSimple ∧ ∀ t, Inside t → p.strictPath t ∉ d.drawing.support := by
  obtain ⟨z,hz,hu,hv⟩ := hface
  obtain ⟨r,hr,haccessu⟩ := d.exists_access_radius u
  obtain ⟨s,hs,haccessv⟩ := d.exists_access_radius v
  obtain ⟨x,hx,hxu⟩ := Metric.mem_closure_iff.mp hu r hr
  obtain ⟨y,hy,hyv⟩ := Metric.mem_closure_iff.mp hv s hs
  have hxnot : x ∉ d.drawing.support := connectedComponentIn_subset _ _ hx
  have hynot : y ∉ d.drawing.support := connectedComponentIn_subset _ _ hy
  obtain ⟨p⟩ := d.drawing.face_polygonallyConnected hz hx hy
  let l : Polygonal.Chain Set.univ (d.drawing.point u) x := .segment (subset_univ _)
  let m : Polygonal.Chain Set.univ x y := p.mono (subset_univ _)
  let r : Polygonal.Chain Set.univ y (d.drawing.point v) := .segment (subset_univ _)
  have hl : l.support = [d.drawing.point u -[ℝ] x] := by
    rw [← Polygonal.Chain.range_strictPath]
    exact Path.range_segment _ _
  have hr : r.support = [d.drawing.point v -[ℝ] y] := by
    rw [← Polygonal.Chain.range_strictPath]
    change Set.range (Path.segment y (d.drawing.point v)) = _
    rw [Path.range_segment,segment_symm]
  have hm : m.support ⊆ d.drawing.supportᶜ :=
    (show m.support = p.support from p.support_mono _).subset.trans
      (p.support_subset.trans (connectedComponentIn_subset _ _))
  obtain ⟨q,hq,hqsub⟩ := ((l.append m).append r).exists_simple
  have hinj := q.strictPath_injective hq (d.drawing.point_injective.ne huv)
  refine ⟨q,hq,?_⟩
  intro t ht hmem
  have hqt : q.strictPath t ∈ q.support := by
    rw [← Polygonal.Chain.range_strictPath]
    exact ⟨t,rfl⟩
  have hh := hqsub hqt
  rw [Polygonal.Chain.support_append,Polygonal.Chain.support_append,hl,hr] at hh
  rcases hh with (hh | hh) | hh
  · have heq := haccessu x (by simpa only [dist_comm] using hxu) hxnot _ hh hmem
    have ht0 := hinj (heq.trans q.strictPath.source.symm)
    simp [Inside,ht0] at ht
  · exact hm hh hmem
  · have heq := haccessv y (by simpa only [dist_comm] using hyv) hynot _ hh hmem
    have ht1 := hinj (heq.trans q.strictPath.target.symm)
    simp [Inside,ht1] at ht

/-- Adding one occurrence between cofacial vertices of a finite polygonal
drawing preserves ordinary planarity by the actual external-arc construction. -/
theorem withEdge_planar [Finite V] [Finite E] (d : PolygonalDrawing G)
    {u v : V} (hface : d.drawing.Cofacial u v) (huv : u ≠ v) :
    (G.withEdge u v).Planar := by
  obtain ⟨p,hp,havoid⟩ := d.exists_external_arc hface huv
  exact ⟨d.drawing.withEdge p.strictPath
    (p.strictPath_injective hp (d.drawing.point_injective.ne huv)) havoid⟩

end PolygonalDrawing
end PlanarHom.MultiGraph

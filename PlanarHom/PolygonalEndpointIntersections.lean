import PlanarHom.PolygonalDrawingIncidence
import PlanarHom.PolygonalStripCompatibility

/-!
# Actual straight-piece intersections in an ordinary polygonal drawing

The original drawing's interior injectivity implies that distinct pieces meet
only at endpoints. Convexity then rules out two distinct intersection points,
so the precise EndpointIntersections premise of the strip construction follows
without an additional drawing or ribbon assumption.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Chain
variable {U : Set X} {x y : X}

/-- A full-chain endpoint cannot lie strictly inside any of its straight pieces,
including when the full chain is a closed graph loop. -/
theorem graphArc_endpoint_segment_contact (p : Chain U x y) (hp : GraphArc p.strictPath)
    {a b z : X} (hab : (a, b) ∈ p.segments) (hend : z = x ∨ z = y)
    (hz : z ∈ [a -[ℝ] b]) : z = a ∨ z = b := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hline⟩ := hz
  by_cases ht0 : t = 0
  · exact Or.inl (by simpa [ht0] using hline.symm)
  · by_cases ht1 : t = 1
    · exact Or.inr (by simpa [ht1] using hline.symm)
    · obtain ⟨f, _, hinside, hpath⟩ := p.segment_subpath hab
      let u : I := ⟨t, ht⟩
      have hu : MultiGraph.Inside u :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      have hfi := hinside u hu
      have hvalue : p.strictPath (f u) = z := (hpath u).trans hline
      have hends : f u = 0 ∨ f u = 1 := by
        rcases hend with hx | hy
        · rcases hp (f u) 0 (hvalue.trans (hx.trans p.strictPath.source.symm)) with h | ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inl h
          · exact Or.inr h
        · rcases hp (f u) 1 (hvalue.trans (hy.trans p.strictPath.target.symm)) with h | ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inr h
          · exact Or.inl h
          · exact Or.inr h
      rcases hends with h | h <;> simp [MultiGraph.Inside, h] at hfi

/-- Different directed pieces of one graph arc have only endpoint contacts. -/
theorem graphArc_segment_contacts (p : Chain U x y) (hp : GraphArc p.strictPath)
    (e f : X × X) (he : e ∈ p.segments) (hf : f ∈ p.segments) (hef : e ≠ f)
    (z : X) (hz : z ∈ [e.1 -[ℝ] e.2]) (hz' : z ∈ [f.1 -[ℝ] f.2]) :
    (z = e.1 ∨ z = e.2) ∧ (z = f.1 ∨ z = f.2) := by
  induction p generalizing e f with
  | nil => simp [segments] at he
  | @cons x a y h p ih =>
      cases p with
      | nil a ha =>
          have heq : e = (x, a) := by simpa [segments] using he
          have hfq : f = (x, a) := by simpa [segments] using hf
          exact (hef (heq.trans hfq.symm)).elim
      | @cons a b y k q =>
          let tail := Chain.cons k q
          have ht : GraphArc tail.strictPath := graphArc_of_injective hp.right_injective
          have hfirst (g : X × X) (hg : g ∈ tail.segments) (v : X)
              (hv : v ∈ [x -[ℝ] a]) (hvg : v ∈ [g.1 -[ℝ] g.2]) :
              (v = x ∨ v = a) ∧ (v = g.1 ∨ v = g.2) := by
            have hc := hp.component_intersection v
              (by simpa only [Path.range_segment] using hv)
              (by rw [range_strictPath]; exact tail.segment_subset_support hg hvg)
            rcases hc with hjoin | ⟨hstart, hloop⟩
            · exact ⟨Or.inr hjoin,
                tail.graphArc_endpoint_segment_contact ht hg (Or.inl hjoin) hvg⟩
            · exact ⟨Or.inl hstart,
                tail.graphArc_endpoint_segment_contact ht hg (Or.inr (hstart.trans hloop)) hvg⟩
          rcases List.mem_cons.mp he with he | he <;> rcases List.mem_cons.mp hf with hf | hf
          · exact (hef (he.trans hf.symm)).elim
          · subst e
            exact hfirst f hf z hz hz'
          · subst f
            exact (hfirst e he z hz' hz).symm
          · exact ih ht e f he hf hef hz hz'

end Chain

/-- If an intersection of two segments is confined to the first segment's two
endpoints, it cannot contain both: their midpoint would be a third point. -/
theorem segment_intersection_subsingleton (P Q R S : X) (hPQ : P ≠ Q)
    (hcontact : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [R -[ℝ] S] → z = P ∨ z = Q) :
    ∀ v, v ∈ [P -[ℝ] Q] → v ∈ [R -[ℝ] S] →
      ∀ w, w ∈ [P -[ℝ] Q] → w ∈ [R -[ℝ] S] → w = v := by
  have hnot : ¬ (P ∈ [R -[ℝ] S] ∧ Q ∈ [R -[ℝ] S]) := by
    rintro ⟨hP, hQ⟩
    let M := AffineMap.lineMap P Q (1 / 2 : ℝ)
    have hM : M ∈ [P -[ℝ] Q] := by
      rw [segment_eq_image_lineMap]
      exact ⟨1 / 2, by constructor <;> norm_num, rfl⟩
    have hM' : M ∈ [R -[ℝ] S] := (convex_segment R S).segment_subset hP hQ hM
    rcases hcontact M hM hM' with hMP | hMQ
    · have he := AffineMap.lineMap_injective ℝ hPQ
        (hMP.trans (AffineMap.lineMap_apply_zero P Q).symm)
      norm_num at he
    · have he := AffineMap.lineMap_injective ℝ hPQ
        (hMQ.trans (AffineMap.lineMap_apply_one P Q).symm)
      norm_num at he
  intro v hv hv' w hw hw'
  rcases hcontact v hv hv' with hvP | hvQ <;> rcases hcontact w hw hw' with hwP | hwQ
  · exact hwP.trans hvP.symm
  · exact (hnot ⟨hvP ▸ hv', hwQ ▸ hw'⟩).elim
  · exact (hnot ⟨hwP ▸ hw', hvQ ▸ hv'⟩).elim
  · exact hwQ.trans hvQ.symm

end PlanarHom.Polygonal

namespace PlanarHom.MultiGraph.PolygonalDrawing
open Polygonal
variable {V E : Type*} {G : MultiGraph V E}

/-- Distinct straight pieces in an ordinary drawing meet only at their actual
endpoints, whether they belong to the same graph edge or different edges. -/
theorem segment_endpoint_contacts (d : PolygonalDrawing G)
    (e f : Plane × Plane) (he : e ∈ d.segmentSet) (hf : f ∈ d.segmentSet) (hef : e ≠ f)
    (z : Plane) (hz : z ∈ [e.1 -[ℝ] e.2]) (hz' : z ∈ [f.1 -[ℝ] f.2]) :
    (z = e.1 ∨ z = e.2) ∧ (z = f.1 ∨ z = f.2) := by
  obtain ⟨i, hei⟩ := he
  obtain ⟨j, hfj⟩ := hf
  by_cases hij : i = j
  · subst j
    exact (d.chain i).graphArc_segment_contacts (d.chain_graphArc i) e f hei hfj hef z hz hz'
  · have hhost : z ∈ d.hostSet := by
      by_contra hn
      exact hij (d.edge_unique_at_nonhost hn ((d.chain i).segment_subset_support hei hz)
        ((d.chain j).segment_subset_support hfj hz'))
    exact ⟨(d.host_segment_contact ⟨i, hei⟩ hhost hz).imp Eq.symm Eq.symm,
      (d.host_segment_contact ⟨j, hfj⟩ hhost hz').imp Eq.symm Eq.symm⟩

/-- The precise endpoint-intersection property is a theorem of the original
ordinary polygonal drawing, with no additional geometric certificate premise. -/
theorem endpointIntersections (d : PolygonalDrawing G) : EndpointIntersections d.segmentSet := by
  intro e he f hf hef
  by_cases hdis : Disjoint [e.1 -[ℝ] e.2] [f.1 -[ℝ] f.2]
  · exact Or.inl hdis
  · obtain ⟨X, hX, hX'⟩ := Set.not_disjoint_iff.mp hdis
    have hc := d.segment_endpoint_contacts e f he hf hef X hX hX'
    refine Or.inr ⟨X, hc.1.imp Eq.symm Eq.symm, hc.2.imp Eq.symm Eq.symm, ?_⟩
    exact segment_intersection_subsingleton e.1 e.2 f.1 f.2 (d.segment_ne he)
      (fun z hz hz' => (d.segment_endpoint_contacts e f he hf hef z hz hz').1) X hX hX'

end PlanarHom.MultiGraph.PolygonalDrawing

import PlanarHom.PlanarRadialTails
import PlanarHom.PolygonalArc
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Disjoint open polygonal-replacement corridors

Compact separation and connected components produce pairwise-disjoint open
connected neighborhoods of the trimmed middle arcs. Each corridor avoids every
original vertex and every other occurrence's straight radial tail. The actual
polygonal connectivity/loop-erasure theorem then gives simple polygonal middle
paths inside those neighborhoods.
-/

noncomputable section
open Set unitInterval Metric
open Classical
namespace PlanarHom.MultiGraph.PlaneDrawing.Trimming
variable {V E : Type*} {G : MultiGraph V E} {d : PlaneDrawing G} {r : ℝ}
variable (T : d.Trimming r)

/-- Closed sets a middle-arc perturbation must avoid. -/
def corridorForbidden (e : E) : Set Plane :=
  Set.range d.point ∪ ⋃ p : {p : E × Bool // p.1 ≠ e}, T.radial p.1

theorem isCompact_corridorForbidden [Finite V] [Finite E] (e : E) :
    IsCompact (T.corridorForbidden e) :=
  (Set.finite_range d.point).isCompact.union
    (isCompact_iUnion (fun p => T.isCompact_radial p.1))

theorem middle_disjoint_corridorForbidden (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) (e : E) :
    Disjoint (T.middle e) (T.corridorForbidden e) := by
  apply Set.disjoint_left.mpr
  rintro x hx (⟨v,rfl⟩ | hrad)
  · exact T.point_notMem_middle e v hx
  · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hrad
    exact Set.disjoint_left.mp (T.middle_disjoint_other_radial hr0 hr (Ne.symm p.2)) hx hp

/-- Geometric neighborhoods, with every separation conclusion proved below. -/
structure Corridors where
  region : E → Set Plane
  isOpen : ∀ e, IsOpen (region e)
  isConnected : ∀ e, IsConnected (region e)
  contains_middle : ∀ e, T.middle e ⊆ region e
  pairwise_disjoint : ∀ e f, e ≠ f → Disjoint (region e) (region f)
  avoids_forbidden : ∀ e, region e ⊆ (T.corridorForbidden e)ᶜ

/-- Actual existence of connected open corridors from finite ordinary drawing
data. No planar-neighborhood theorem is assumed. -/
theorem exists_corridors [Finite V] [Finite E] (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) :
    Nonempty T.Corridors := by
  letI : LocallyConnectedSpace Plane :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr (by
      intro x U hU
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
      exact ⟨Metric.ball x ε,hsub,isOpen_ball,Metric.mem_ball_self hε,
        (convex_ball x ε).isConnected ⟨x,Metric.mem_ball_self hε⟩⟩)
  have hforbid : ∀ e, ∃ ε : ℝ, 0 < ε ∧
      thickening ε (T.middle e) ⊆ (T.corridorForbidden e)ᶜ := by
    intro e
    apply (T.isCompact_middle e).exists_thickening_subset_open
      (T.isCompact_corridorForbidden e).isClosed.isOpen_compl
    exact disjoint_left.mp (T.middle_disjoint_corridorForbidden hr0 hr e)
  have hpair : ∀ p : E × E, ∃ ε : ℝ, 0 < ε ∧
      (p.1 ≠ p.2 → Disjoint (thickening ε (T.middle p.1)) (thickening ε (T.middle p.2))) := by
    rintro ⟨e,f⟩
    by_cases h : e = f
    · exact ⟨1,zero_lt_one,fun he => (he h).elim⟩
    · obtain ⟨ε,hε,hdis⟩ := (T.middle_disjoint h).exists_thickenings
        (T.isCompact_middle e) (T.isCompact_middle f).isClosed
      exact ⟨ε,hε,fun _ => hdis⟩
  choose a ha havoid using hforbid
  choose b hb hdis using hpair
  obtain ⟨α,hα,hαa⟩ := PlaneDrawing.finite_positive_lower_bound a ha
  obtain ⟨β,hβ,hβb⟩ := PlaneDrawing.finite_positive_lower_bound b hb
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  let B : E → Set Plane := fun e => thickening δ (T.middle e)
  let U : E → Set Plane := fun e => connectedComponentIn (B e) (T.port (e,false))
  have hKB : ∀ e, T.middle e ⊆ B e := fun e => self_subset_thickening hδ _
  have hKU : ∀ e, T.middle e ⊆ U e := fun e =>
    (T.isConnected_middle e).isPreconnected.subset_connectedComponentIn (T.port_mem_middle (e,false)) (hKB e)
  have hBU : ∀ e, U e ⊆ B e := fun e => connectedComponentIn_subset _ _
  refine ⟨⟨U,?_,?_,hKU,?_,?_⟩⟩
  · intro e
    exact (isOpen_thickening : IsOpen (B e)).connectedComponentIn
  · intro e
    exact isConnected_connectedComponentIn_iff.mpr (hKB e (T.port_mem_middle (e,false)))
  · intro e f hef
    have hδb : δ ≤ b (e,f) := (min_le_right _ _).trans (hβb (e,f))
    exact (hdis (e,f) hef).mono
      ((hBU e).trans (thickening_mono hδb _))
      ((hBU f).trans (thickening_mono hδb _))
  · intro e
    exact (hBU e).trans ((thickening_mono ((min_le_left _ _).trans (hαa e)) _).trans (havoid e))

namespace Corridors
variable {T} (C : T.Corridors)

theorem vertex_notMem (e : E) (v : V) : d.point v ∉ C.region e := by
  intro h
  exact C.avoids_forbidden e h (Or.inl ⟨v,rfl⟩)

theorem disjoint_other_radial {e : E} {p : E × Bool} (he : p.1 ≠ e) :
    Disjoint (C.region e) (T.radial p) := by
  apply Set.disjoint_left.mpr
  intro x hx hp
  exact C.avoids_forbidden e hx (Or.inr (Set.mem_iUnion.mpr ⟨⟨p,he⟩,hp⟩))

theorem left_mem (e : E) : T.port (e,false) ∈ C.region e :=
  C.contains_middle e (T.port_mem_middle (e,false))

theorem right_mem (e : E) : T.port (e,true) ∈ C.region e :=
  C.contains_middle e (T.port_mem_middle (e,true))

/-- Genuine simple finite polygonal middle paths in the disjoint corridors. -/
theorem exists_simple_middle (e : E) :
    ∃ p : Polygonal.Chain (C.region e) (T.port (e,false)) (T.port (e,true)),
      p.IsSimple ∧ Function.Injective p.strictPath ∧ Set.range p.strictPath ⊆ C.region e := by
  apply Polygonal.exists_injective_polygonal_arc (C.isOpen e) (C.isConnected e).isPreconnected
    (C.left_mem e) (C.right_mem e)
  exact T.port_injective.ne (by simp)

end Corridors
end PlanarHom.MultiGraph.PlaneDrawing.Trimming

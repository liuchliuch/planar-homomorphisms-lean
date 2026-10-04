import PlanarHom.PolygonalStrips

/-! NEW dependency extraction from the complete recovered CircleArches source.
The Cayley-map definitions and proofs below are copied verbatim. No statement or
hypothesis is removed. They are independent of the missing arch-routing imports.
The full original is retained in reference_sources with SHA provenance. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph

def cayleyDen (p : Plane) : ℝ := (p.1+1)^2+p.2^2

def diskMap (p : Plane) : Plane :=
  (2*p.2/cayleyDen p,(p.1^2+p.2^2-1)/cayleyDen p)

def inverseDen (q : Plane) : ℝ := (1-q.2)^2+q.1^2

def halfPlaneMap (q : Plane) : Plane :=
  ((1-q.1^2-q.2^2)/inverseDen q,2*q.1/inverseDen q)

theorem cayleyDen_pos (p : Plane) (hp : 0≤p.1) : 0<cayleyDen p := by
  unfold cayleyDen
  nlinarith [sq_nonneg p.2,sq_nonneg p.1]

theorem inverseDen_diskMap (p : Plane) (hp : cayleyDen p≠0) :
    inverseDen (diskMap p)=4/cayleyDen p := by
  unfold inverseDen diskMap
  dsimp
  field_simp
  unfold cayleyDen
  ring

theorem diskMap_norm_sq (p : Plane) (hp : cayleyDen p≠0) :
    (diskMap p).1^2+(diskMap p).2^2=1-4*p.1/cayleyDen p := by
  unfold diskMap
  dsimp
  field_simp
  unfold cayleyDen
  ring

theorem halfPlaneMap_diskMap (p : Plane) (hp : 0≤p.1) : halfPlaneMap (diskMap p)=p := by
  have hn : cayleyDen p≠0 := ne_of_gt (cayleyDen_pos p hp)
  unfold halfPlaneMap
  rw [inverseDen_diskMap p hn]
  apply Prod.ext
  · change (1-(diskMap p).1^2-(diskMap p).2^2)/(4/cayleyDen p)=p.1
    have hnum : 1-(diskMap p).1^2-(diskMap p).2^2=4*p.1/cayleyDen p := by
      have := diskMap_norm_sq p hn
      linarith
    rw [hnum]
    field_simp
  · change 2*(2*p.2/cayleyDen p)/(4/cayleyDen p)=p.2
    field_simp
    ring

theorem diskMap_injOn : Set.InjOn diskMap {p : Plane | 0≤p.1} := by
  intro p hp q hq he
  calc
    p = halfPlaneMap (diskMap p) := (halfPlaneMap_diskMap p hp).symm
    _ = halfPlaneMap (diskMap q) := congrArg halfPlaneMap he
    _ = q := halfPlaneMap_diskMap q hq

theorem diskMap_boundary (y : ℝ) : (diskMap (0,y)).1^2+(diskMap (0,y)).2^2=1 := by
  simpa using diskMap_norm_sq (0,y) (ne_of_gt (cayleyDen_pos (0,y) le_rfl))

theorem diskMap_interior (p : Plane) (hp : 0<p.1) :
    (diskMap p).1^2+(diskMap p).2^2<1 := by
  rw [diskMap_norm_sq p (ne_of_gt (cayleyDen_pos p hp.le))]
  have hh : 0<4*p.1/cayleyDen p := div_pos (by positivity) (cayleyDen_pos p hp.le)
  linarith

end PlanarHom.RadialPottsAssemblyGeometry

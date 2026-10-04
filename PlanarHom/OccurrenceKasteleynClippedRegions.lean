import PlanarHom.OccurrenceKasteleynIncomingRootward

/-! NEW actual disk-and-band regions for finite subtree routing. Disjoint
vertex and edge sets with no cross-incidence give disjoint closed geometric
regions, directly from recovered clipping rather than an embedding premise. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

def hostDisk (v : V) : Set Plane := {x | rayLength (x-d.drawing.point v)≤C.radius}

def clippedRegion (vertices : Set V) (edges : Set E) : Set Plane :=
  {x | (∃ v∈vertices, x∈C.hostDisk v) ∨ (∃ e∈edges, x∈Set.range (C.band Function.injective_id e))}

theorem band_disjoint_nonincident_disk (e : E) (v : V) (hs : G.src e≠v) (ht : G.dst e≠v) :
    Disjoint (Set.range (C.band Function.injective_id e)) (C.hostDisk v) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,rfl⟩ hx
  have he : rayLength (C.band Function.injective_id e p-d.drawing.point v)=C.radius :=
    le_antisymm hx (C.band_radius_le Function.injective_id e p v)
  rcases (C.band_on_circle_iff Function.injective_id e p v).mp he with h | h
  · exact hs h.2
  · exact ht h.2

theorem clippedRegions_disjoint {S T : Set V} {A B : Set E}
    (hst : Disjoint S T) (hab : Disjoint A B)
    (hat : ∀ e∈A, G.src e∉T ∧ G.dst e∉T)
    (hbs : ∀ e∈B, G.src e∉S ∧ G.dst e∉S) :
    Disjoint (C.clippedRegion S A) (C.clippedRegion T B) := by
  apply Set.disjoint_left.mpr
  rintro x (⟨v,hv,hxv⟩ | ⟨e,he,hxe⟩) (⟨w,hw,hxw⟩ | ⟨f,hf,hxf⟩)
  · have hvw : v≠w := fun h => Set.disjoint_left.mp hst hv (h ▸ hw)
    exact Set.disjoint_left.mp (C.disks_disjoint v w hvw) hxv hxw
  · exact Set.disjoint_left.mp (C.band_disjoint_nonincident_disk f v
      (fun h => (hbs f hf).1 (h.symm ▸ hv)) (fun h => (hbs f hf).2 (h.symm ▸ hv))) hxf hxv
  · exact Set.disjoint_left.mp (C.band_disjoint_nonincident_disk e w
      (fun h => (hat e he).1 (h.symm ▸ hw)) (fun h => (hat e he).2 (h.symm ▸ hw))) hxe hxw
  · have hef : e≠f := fun h => Set.disjoint_left.mp hab he (h ▸ hf)
    exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hef) hxe hxf

theorem clippedRegion_disjoint_band {S : Set V} {A : Set E} (e : E)
    (he : e∉A) (hs : G.src e∉S) (ht : G.dst e∉S) :
    Disjoint (C.clippedRegion S A) (Set.range (C.band Function.injective_id e)) := by
  apply Set.disjoint_left.mpr
  rintro x (⟨v,hv,hxv⟩ | ⟨f,hf,hxf⟩) hxe
  · exact Set.disjoint_left.mp (C.band_disjoint_nonincident_disk e v
      (fun h => hs (h.symm ▸ hv)) (fun h => ht (h.symm ▸ hv))) hxe hxv
  · exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id
      (fun h : f=e => he (h ▸ hf))) hxf hxe

theorem clippedRegion_disjoint_disk {S : Set V} {A : Set E} (v : V) (hv : v∉S)
    (ha : ∀ e∈A, G.src e≠v ∧ G.dst e≠v) :
    Disjoint (C.clippedRegion S A) (C.hostDisk v) := by
  apply Set.disjoint_left.mpr
  rintro x (⟨w,hw,hxw⟩ | ⟨e,he,hxe⟩) hxv
  · exact Set.disjoint_left.mp (C.disks_disjoint w v (fun h => hv (h ▸ hw))) hxw hxv
  · exact Set.disjoint_left.mp (C.band_disjoint_nonincident_disk e v (ha e he).1 (ha e he).2) hxe hxv

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

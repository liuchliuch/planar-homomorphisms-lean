import PlanarHom.PlanarRibbonExistence

/-!
# NEW proof: two-sided occurrence collars and their actual complementary faces

This is new proof reconstruction, not recovered historical source. Starting with
proved pinched ribbons, move the drawing to their middle slices. Each ribbon then
supplies two disjoint continuous side collars of the new drawing. The open sides
avoid the entire graph and lie in actual connected components of its complement;
the entire corresponding edge, endpoints included, borders each assigned face.

This does not claim a two-sided collar of the *unchanged* input drawing, nor a
polygonal output, cyclic face boundary, finite face enumeration, Jordan/Euler
identity, computed planar embedding, or Pfaffian orientation.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph
namespace RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Choose an arbitrary constant transverse slice as the graph centerline. -/
def sliceDrawing (d : RibbonDrawing G) (height : I) : PlaneDrawing G where
  point := d.point
  point_injective := d.point_injective
  curve e := (d.band e).comp (slice height)
  curve_zero e := d.band_zero e height
  curve_one e := d.band_one e height
  interior_injective := by
    intro e f s t hs ht heq
    obtain ⟨hef,hst⟩ := d.band_injective e f (s,height) (t,height) hs ht heq
    exact ⟨hef,congrArg Prod.fst hst⟩
  interior_avoids e t ht v := d.band_avoids e (t,height) ht v

/-- The recentered drawing has the same abstract graph and vertex positions. -/
def centerDrawing (d : RibbonDrawing G) : PlaneDrawing G :=
  d.sliceDrawing PlaneDrawing.half

/-- Transverse coordinate: zero is the centerline on both sides. -/
def sideHeight (positive : Bool) : C(I,I) where
  toFun s := if positive then
    ⟨(1+(s : ℝ))/2,by constructor <;> linarith [s.2.1,s.2.2]⟩
    else ⟨(1-(s : ℝ))/2,by constructor <;> linarith [s.2.1,s.2.2]⟩
  continuous_toFun := by cases positive <;> dsimp <;> fun_prop

@[simp] theorem sideHeight_zero (positive : Bool) : sideHeight positive 0 = PlaneDrawing.half := by
  cases positive <;> apply Subtype.ext <;> norm_num [sideHeight,PlaneDrawing.half]

theorem sideHeight_injective (positive : Bool) : Function.Injective (sideHeight positive) := by
  intro s t h
  have h' := congrArg (fun x : I => (x : ℝ)) h
  apply Subtype.ext
  cases positive <;> dsimp [sideHeight] at h' <;> linarith

theorem sideHeight_ne_half (positive : Bool) {s : I} (hs : 0 < (s : ℝ)) :
    sideHeight positive s ≠ PlaneDrawing.half := by
  intro h
  have h' := congrArg (fun x : I => (x : ℝ)) h
  cases positive <;> dsimp [sideHeight,PlaneDrawing.half] at h' <;> linarith

/-- Opposite closed half-ribbons meet only on their common centerline. -/
theorem sideHeight_eq_iff {s t : I} :
    sideHeight false s = sideHeight true t ↔ s = 0 ∧ t = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun x : I => (x : ℝ)) h
    dsimp [sideHeight] at h'
    constructor <;> apply Subtype.ext <;> dsimp <;> linarith [s.2.1,t.2.1]
  · rintro ⟨rfl,rfl⟩
    simp

/-- Both side collars are concrete continuous maps on a closed square. -/
def sideBand (d : RibbonDrawing G) (positive : Bool) (e : E) : C(I × I,Plane) :=
  (d.band e).comp {
    toFun := fun p => (p.1,sideHeight positive p.2)
    continuous_toFun := by fun_prop }

@[simp] theorem sideBand_center (d : RibbonDrawing G) (positive : Bool) (e : E) (t : I) :
    d.sideBand positive e (t,0) = d.centerDrawing.curve e t := by
  change d.band e (t,sideHeight positive 0) = d.band e (t,PlaneDrawing.half)
  rw [sideHeight_zero]

/-- Each closed half-ribbon separately retains all original ribbon conditions. -/
def sideRibbon (d : RibbonDrawing G) (positive : Bool) : RibbonDrawing G where
  point := d.point
  point_injective := d.point_injective
  band := d.sideBand positive
  band_zero e s := d.band_zero e (sideHeight positive s)
  band_one e s := d.band_one e (sideHeight positive s)
  band_injective := by
    intro e f p q hp hq heq
    obtain ⟨hef,hpq⟩ := d.band_injective e f
      (p.1,sideHeight positive p.2) (q.1,sideHeight positive q.2) hp hq heq
    have hfst := congrArg Prod.fst hpq
    have hsnd := congrArg Prod.snd hpq
    exact ⟨hef,Prod.ext hfst (sideHeight_injective positive hsnd)⟩
  band_avoids e p hp v := d.band_avoids e (p.1,sideHeight positive p.2) hp v

/-- An intersection of opposite collars is precisely on the original occurrence
and its centerline. No distinct-face claim is made: bridges can border one face. -/
theorem opposite_sideBand_eq (d : RibbonDrawing G) {e f : E} {p q : I × I}
    (hp : Inside p.1) (hq : Inside q.1)
    (heq : d.sideBand false e p = d.sideBand true f q) :
    e = f ∧ p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 := by
  obtain ⟨hef,hpq⟩ := d.band_injective e f
    (p.1,sideHeight false p.2) (q.1,sideHeight true q.2) hp hq heq
  have hfst := congrArg Prod.fst hpq
  have hsnd := congrArg Prod.snd hpq
  exact ⟨hef,hfst,sideHeight_eq_iff.mp hsnd⟩

/-- Every nonzero transverse point with interior longitudinal coordinate avoids
all vertices and every edge occurrence of the recentered graph. -/
theorem sideBand_not_mem_support (d : RibbonDrawing G) (positive : Bool) (e : E)
    (t s : I) (ht : Inside t) (hs : 0 < (s : ℝ)) :
    d.sideBand positive e (t,s) ∉ d.centerDrawing.support := by
  rintro (⟨v,hv⟩ | hcurve)
  · exact d.band_avoids e (t,sideHeight positive s) ht v hv.symm
  · obtain ⟨f,u,hu⟩ := Set.mem_iUnion.mp hcurve
    by_cases h0 : u = 0
    · rw [h0,d.centerDrawing.curve_zero] at hu
      exact d.band_avoids e (t,sideHeight positive s) ht (G.src f) hu.symm
    by_cases h1 : u = 1
    · rw [h1,d.centerDrawing.curve_one] at hu
      exact d.band_avoids e (t,sideHeight positive s) ht (G.dst f) hu.symm
    have hui := PlaneDrawing.inside_of_ne_endpoints h0 h1
    have heq : d.band e (t,sideHeight positive s) = d.band f (u,PlaneDrawing.half) := hu.symm
    have hheight := congrArg Prod.snd (d.band_injective e f _ _ ht hui heq).2
    exact sideHeight_ne_half positive hs hheight

/-- The parameter domain used for connected, nonzero open sides. -/
def sideDomain : Set (I × I) := Set.Ioo 0 1 ×ˢ Set.Ioo 0 1

/-- The image of one open side in the actual plane. -/
def sideRegion (d : RibbonDrawing G) (positive : Bool) (e : E) : Set Plane :=
  d.sideBand positive e '' sideDomain

private theorem mem_sideDomain_inside {p : I × I} (hp : p ∈ sideDomain) :
    Inside p.1 ∧ Inside p.2 := by
  exact hp

/-- Every open side is nonempty and connected, including sides of loops. -/
theorem sideRegion_isConnected (d : RibbonDrawing G) (positive : Bool) (e : E) :
    IsConnected (d.sideRegion positive e) := by
  apply IsConnected.image _ _ (d.sideBand positive e).continuous.continuousOn
  exact (isConnected_Ioo (show (0 : I) < 1 by norm_num)).prod
    (isConnected_Ioo (show (0 : I) < 1 by norm_num))

theorem sideRegion_subset_compl (d : RibbonDrawing G) (positive : Bool) (e : E) :
    d.sideRegion positive e ⊆ d.centerDrawing.supportᶜ := by
  rintro _ ⟨⟨t,s⟩,hp,rfl⟩
  exact d.sideBand_not_mem_support positive e t s (mem_sideDomain_inside hp).1
    (mem_sideDomain_inside hp).2.1

/-- Different occurrence-sides have disjoint open collar regions. -/
theorem sideRegion_disjoint (d : RibbonDrawing G) {b c : Bool} {e f : E}
    (hne : (e,b) ≠ (f,c)) : Disjoint (d.sideRegion b e) (d.sideRegion c f) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨p,hp,hpe⟩ ⟨q,hq,hqf⟩
  have heq := hpe.trans hqf.symm
  have hpi := mem_sideDomain_inside hp
  have hqi := mem_sideDomain_inside hq
  have h := d.band_injective e f (p.1,sideHeight b p.2)
    (q.1,sideHeight c q.2) hpi.1 hqi.1 heq
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · have hz := (sideHeight_eq_iff.mp (congrArg Prod.snd h.2)).1
      exact (ne_of_gt hpi.2.1 (congrArg (fun s : I => (s : ℝ)) hz)).elim
    · have hz := (sideHeight_eq_iff.mp (congrArg Prod.snd h.2).symm).2
      exact (ne_of_gt hpi.2.1 (congrArg (fun s : I => (s : ℝ)) hz)).elim
    · rfl
  exact hne (Prod.ext h.1 hbc)

/-- The entire closed edge curve borders either side, even at its host endpoints. -/
theorem curve_mem_closure_sideRegion (d : RibbonDrawing G) (positive : Bool) (e : E) (t : I) :
    d.centerDrawing.curve e t ∈ closure (d.sideRegion positive e) := by
  rw [← d.sideBand_center positive e t]
  apply image_closure_subset_closure_image (d.sideBand positive e).continuous
  refine ⟨(t,0),?_,rfl⟩
  rw [sideDomain,closure_prod_eq,closure_Ioo (show (0 : I) ≠ 1 by norm_num)]
  exact ⟨⟨bot_le,le_top⟩,⟨le_rfl,bot_le⟩⟩

/-- A concrete witness in the connected open side, requiring no choice of face. -/
def sideWitness (d : RibbonDrawing G) (positive : Bool) (e : E) : Plane :=
  d.sideBand positive e (PlaneDrawing.half,PlaneDrawing.half)

theorem sideWitness_mem (d : RibbonDrawing G) (positive : Bool) (e : E) :
    d.sideWitness positive e ∈ d.sideRegion positive e := by
  exact ⟨(PlaneDrawing.half,PlaneDrawing.half),
    ⟨PlaneDrawing.half_inside,PlaneDrawing.half_inside⟩,rfl⟩

/-- A face is the actual connected component of the graph complement. -/
def sideFace (d : RibbonDrawing G) (positive : Bool) (e : E) : Set Plane :=
  connectedComponentIn d.centerDrawing.supportᶜ (d.sideWitness positive e)

theorem sideRegion_subset_sideFace (d : RibbonDrawing G) (positive : Bool) (e : E) :
    d.sideRegion positive e ⊆ d.sideFace positive e :=
  (d.sideRegion_isConnected positive e).isPreconnected.subset_connectedComponentIn
    (d.sideWitness_mem positive e) (d.sideRegion_subset_compl positive e)

theorem sideFace_isConnected (d : RibbonDrawing G) (positive : Bool) (e : E) :
    IsConnected (d.sideFace positive e) :=
  isConnected_connectedComponentIn_iff.mpr
    (d.sideRegion_subset_compl positive e (d.sideWitness_mem positive e))

/-- The assigned actual face does not depend on which point of its side is used. -/
theorem sideFace_eq_at_mem (d : RibbonDrawing G) (positive : Bool) (e : E)
    {z : Plane} (hz : z ∈ d.sideRegion positive e) :
    d.sideFace positive e = connectedComponentIn d.centerDrawing.supportᶜ z :=
  connectedComponentIn_eq (d.sideRegion_subset_sideFace positive e hz)

/-- Every point of the occurrence, endpoints included, is in this face closure. -/
theorem curve_mem_closure_sideFace (d : RibbonDrawing G) (positive : Bool) (e : E) (t : I) :
    d.centerDrawing.curve e t ∈ closure (d.sideFace positive e) :=
  closure_mono (d.sideRegion_subset_sideFace positive e)
    (d.curve_mem_closure_sideRegion positive e t)

/-- The source and target really border the same assigned complementary face. -/
theorem endpoints_cofacial (d : RibbonDrawing G) (positive : Bool) (e : E) :
    d.centerDrawing.Cofacial (G.src e) (G.dst e) := by
  refine ⟨d.sideWitness positive e,
    d.sideRegion_subset_compl positive e (d.sideWitness_mem positive e),?_,?_⟩
  · simpa only [d.centerDrawing.curve_zero] using d.curve_mem_closure_sideFace positive e 0
  · simpa only [d.centerDrawing.curve_one] using d.curve_mem_closure_sideFace positive e 1

end RibbonDrawing
end PlanarHom.MultiGraph

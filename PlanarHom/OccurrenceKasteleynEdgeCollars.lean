import PlanarHom.PolygonalOppositeStripSeparation
import PlanarHom.OccurrenceKasteleynPeeling

/-!
# NEW proof: original-drawing signed normal collars

This reconstructs the normal/width API actually required by the recovered ribbon
endpoint consumers. Both numerical widths and mixed-sign center compatibility
are derived from finite polygonal incidence. A curve-preserving refinement gives
non-host endpoints for every straight piece; no embedding/orientation certificate
or local separation conclusion is assumed from the graph's planarity promise.
-/
noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal.Chain
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {U : Set X} {x y : X}

/-- Finite polygonal interpolation is affine for every real coefficient,
including the negative coefficient needed to compare opposite ribbon sides. -/
theorem strictPath_mapVertices_affine (p : Chain U x y) (f : X → X) (c : ℝ) (t : I) :
    (p.mapVertices (fun v => v+c • (f v-v))).strictPath t =
      p.strictPath t+c • ((p.mapVertices f).strictPath t-p.strictPath t) := by
  induction p generalizing t with
  | nil => rfl
  | @cons x a y h p ih =>
    cases p with
    | nil a ha =>
      simp only [strictPath,mapVertices,Path.segment_apply,AffineMap.lineMap_apply_module]
      module
    | @cons a b y k q =>
      by_cases ht : (t : ℝ) ≤ 1/2
      · simp only [strictPath,mapVertices,Path.trans_apply,dif_pos ht,
          Path.segment_apply,AffineMap.lineMap_apply_module]
        module
      · let u : I := ⟨2*(t : ℝ)-1,by constructor <;> linarith [t.2.2]⟩
        simpa only [strictPath,mapVertices,Path.trans_apply,dif_neg ht] using ih u

end PlanarHom.Polygonal.Chain

namespace PlanarHom.MultiGraph.PolygonalDrawing
open Polygonal
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- Actual shared normal, common width, and proved same-side/cross-side strip
conditions on the unchanged polygonal drawing. -/
structure TwoSidedStripData (d : PolygonalDrawing G) where
  normal : Plane → Plane
  width : ℝ
  width_pos : 0<width
  normal_host : ∀ x ∈ d.hostSet, normal x=0
  cross_start : ∀ a b, (a,b) ∈ d.segmentSet → a ∉ d.hostSet → 0<cross (b-a) (normal a)
  cross_end : ∀ a b, (a,b) ∈ d.segmentSet → b ∉ d.hostSet → 0<cross (b-a) (normal b)
  free_endpoints : ∀ a b, (a,b) ∈ d.segmentSet → a ∉ d.hostSet ∨ b ∉ d.hostSet
  positive_good : GoodStripWidth d.segmentFinset d.hostSet normal width
  negative_good : GoodStripWidth d.segmentFinset d.hostSet (fun x => -normal x) width
  opposite_centers : ∀ e ∈ d.segmentFinset, ∀ f ∈ d.segmentFinset,
    StripCentersAgree e.1 e.2 (width • normal e.1) (width • normal e.2)
      f.1 f.2 (width • -normal f.1) (width • -normal f.2)

namespace TwoSidedStripData
variable {d : PolygonalDrawing G}

def signedNormal (D : d.TwoSidedStripData) (positive : Bool) (x : Plane) : Plane :=
  if positive then D.normal x else -D.normal x

theorem signedNormal_host (D : d.TwoSidedStripData) (positive : Bool) (x : Plane) (hx : x ∈ d.hostSet) :
    D.signedNormal positive x=0 := by
  cases positive <;> simp [signedNormal,D.normal_host x hx]

def sideRibbon (D : d.TwoSidedStripData) (positive : Bool) : RibbonDrawing G :=
  d.ribbonOfGoodWidth d.segmentFinset (fun e _ h => d.chain_segment_mem_finset e h)
    (D.signedNormal positive) D.width (D.signedNormal_host positive)
    (by cases positive; exact D.negative_good; exact D.positive_good)

@[simp] theorem sideRibbon_point (D : d.TwoSidedStripData) (positive : Bool) (v : V) :
    (D.sideRibbon positive).point v = d.drawing.point v := rfl

/-- The centerline is exactly the original parametrized curve, not a redrawing. -/
@[simp] theorem sideRibbon_center (D : d.TwoSidedStripData) (positive : Bool) (e : E) (t : I) :
    (D.sideRibbon positive).band e (t,0) = d.drawing.curve e t := by
  change (d.chain e).vertexBand (fun v => v+D.width • D.signedNormal positive v) (t,0) = _
  rw [Chain.vertexBand_zero_transverse,d.curve_eq]
  rfl

/-- Mixed-side intersections recover the same original occurrence and center
parameter. The transverse conclusion is proved below from actual interpolation. -/
theorem opposite_center_parameters (D : d.TwoSidedStripData) {e f : E} {t u s v : I}
    (ht : Inside t) (hu : Inside u)
    (h : (D.sideRibbon true).band e (t,s) = (D.sideRibbon false).band f (u,v)) :
    e=f ∧ t=u := by
  obtain ⟨a,b,hab,l,hl,hband⟩ := (d.chain e).vertexBand_offset_joint_strip
    (d.chain_length_ne_zero e) D.normal D.width t
  obtain ⟨c,k,hck,m,hm,hband'⟩ := (d.chain f).vertexBand_offset_joint_strip
    (d.chain_length_ne_zero f) (fun x => -D.normal x) D.width u
  have he : (a,b) ∈ d.segmentFinset := d.chain_segment_mem_finset e hab
  have hf : (c,k) ∈ d.segmentFinset := d.chain_segment_mem_finset f hck
  have hc := D.opposite_centers (a,b) he (c,k) hf (l,s) (m,v)
    ((hband s).symm.trans (h.trans (hband' v)))
  apply d.drawing.interior_injective e f t u ht hu
  rw [d.curve_eq,d.curve_eq]
  exact hl.trans (hc.trans hm.symm)


/-- The two literal signed bands meet only on their common original centerline.
This rules out cross-side intersections, not just intersections within each side. -/
theorem sideRibbon_opposite_intersection (D : d.TwoSidedStripData) {e f : E} {t u s v : I}
    (ht : Inside t) (hu : Inside u)
    (h : (D.sideRibbon true).band e (t,s) = (D.sideRibbon false).band f (u,v)) :
    e=f ∧ t=u ∧ s=0 ∧ v=0 := by
  obtain ⟨rfl,rfl⟩ := D.opposite_center_parameters ht hu h
  let p := d.chain e
  let x := p.strictPath t
  let delta := (p.mapVertices (fun z => z+D.width • D.normal z)).strictPath t-x
  have hn : (p.mapVertices (fun z => z+D.width • -D.normal z)).strictPath t = x-delta := by
    have hh := p.strictPath_mapVertices_affine (fun z => z+D.width • D.normal z) (-1) t
    have hg : (fun z => z+(-1 : ℝ) • (z+D.width • D.normal z-z)) =
        (fun z => z+D.width • -D.normal z) := by funext z; module
    have hm := congrArg (fun f : Plane → Plane => (p.mapVertices f).strictPath t) hg
    have hh' := hm.symm.trans hh
    change (p.mapVertices (fun z => z+D.width • -D.normal z)).strictPath t =
      x+(-1 : ℝ) • delta at hh'
    simpa only [neg_one_smul,sub_eq_add_neg] using hh'
  have heq : x+(s : ℝ) • delta = x+(v : ℝ) • -delta := by
    change p.strictPath t+(s : ℝ) •
      ((p.mapVertices (fun z => z+D.width • D.normal z)).strictPath t-p.strictPath t) =
      p.strictPath t+(v : ℝ) •
      ((p.mapVertices (fun z => z+D.width • -D.normal z)).strictPath t-p.strictPath t) at h
    rw [hn] at h
    change x+(s : ℝ) • delta = x+(v : ℝ) • (x-delta-x) at h
    have hz : x-delta-x = -delta := by abel
    rwa [hz] at h
  have hdelta : delta ≠ 0 := by
    intro hz
    have hband : (D.sideRibbon true).band e (t,0) = (D.sideRibbon true).band e (t,1) := by
      change x+(0 : ℝ) • delta = x+(1 : ℝ) • delta
      simp [hz]
    have hh := (D.sideRibbon true).band_injective e e (t,0) (t,1) ht ht hband
    have h01 : (0 : I) = 1 := congrArg Prod.snd hh.2
    exact zero_ne_one h01
  have hzero : ((s : ℝ)+(v : ℝ)) • delta = 0 := by
    calc
      _ = (x+(s : ℝ) • delta)-(x+(v : ℝ) • -delta) := by module
      _ = 0 := sub_eq_zero.mpr heq
  have hsv : (s : ℝ)+(v : ℝ)=0 := (smul_eq_zero.mp hzero).resolve_right hdelta
  refine ⟨rfl,rfl,Subtype.ext ?_,Subtype.ext ?_⟩ <;> change (_ : ℝ)=0 <;>
    linarith [s.2.1,v.2.1]

/-- Nonzero side heights avoid every occurrence and vertex of the original
unchanged graph, not merely the other bands of the same side. -/
theorem sideRibbon_not_mem_support (D : d.TwoSidedStripData) (positive : Bool) (e : E)
    (t s : I) (ht : Inside t) (hs : 0<(s : ℝ)) :
    (D.sideRibbon positive).band e (t,s) ∉ d.drawing.support := by
  rintro (⟨w,hw⟩ | he)
  · exact (D.sideRibbon positive).band_avoids e (t,s) ht w hw.symm
  · obtain ⟨f,u,hu⟩ := Set.mem_iUnion.mp he
    by_cases h0 : u=0
    · rw [h0,d.drawing.curve_zero] at hu
      exact (D.sideRibbon positive).band_avoids e (t,s) ht (G.src f) hu.symm
    by_cases h1 : u=1
    · rw [h1,d.drawing.curve_one] at hu
      exact (D.sideRibbon positive).band_avoids e (t,s) ht (G.dst f) hu.symm
    have heq : (D.sideRibbon positive).band e (t,s) = (D.sideRibbon positive).band f (u,0) := by
      rw [D.sideRibbon_center]
      exact hu.symm
    have hh := (D.sideRibbon positive).band_injective e f (t,s) (u,0) ht
      (PlaneDrawing.inside_of_ne_endpoints h0 h1) heq
    have hs0 : s=0 := congrArg Prod.snd hh.2
    have hs0' : (s : ℝ)=0 := congrArg (fun t : I => (t : ℝ)) hs0
    linarith

end TwoSidedStripData

/-- Existence from genuine finite piece geometry whenever every piece has a
non-host endpoint, as supplied by the standard curve-preserving refinement. -/
theorem exists_twoSidedStripData (d : PolygonalDrawing G)
    (hfree : ∀ a b, (a,b) ∈ d.segmentSet → a ∉ d.hostSet ∨ b ∉ d.hostSet) :
    Nonempty d.TwoSidedStripData := by
  let S := d.segmentFinset
  have hS : (S : Set (Plane × Plane)) = d.segmentSet := d.coe_segmentFinset
  have hcorner : TwoValentCorners (S : Set (Plane × Plane)) d.hostSet := by rw [hS]; exact d.twoValentCorners
  have hpair : EndpointIntersections (S : Set (Plane × Plane)) := by rw [hS]; exact d.endpointIntersections
  have hne : ∀ e ∈ S, e.1 ≠ e.2 := fun e he => d.segment_ne ((d.mem_segmentFinset e).mp he)
  have hvertex : HostEndpointOnly (S : Set (Plane × Plane)) d.hostSet := by
    intro e he x hx hi
    exact (d.host_segment_contact ((d.mem_segmentFinset e).mp he) hx hi).imp Eq.symm Eq.symm
  have hfree' : ∀ a b, (a,b) ∈ S → a ∉ d.hostSet ∨ b ∉ d.hostSet :=
    fun a b hab => hfree a b ((d.mem_segmentFinset (a,b)).mp hab)
  obtain ⟨N,hzero,hout,hin⟩ := exists_normal_assignment (S : Set (Plane × Plane)) d.hostSet hcorner
  have hgood := eventually_signed_good_strip_width S d.hostSet d.finite_hostSet N
    hcorner hpair hne hvertex hzero hout hin hfree'
  have hcross := eventually_all_opposite_strip_centers S d.hostSet N hcorner hpair hne hzero hout hin
  have hpos : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, 0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,⟨hp,hn⟩,hc⟩ := (hpos.and (hgood.and hcross)).exists
  refine ⟨⟨N,ε,hε,hzero,?_,?_,hfree,hp,hn,hc⟩⟩
  · intro a b hab ha
    exact hout a b ((d.mem_segmentFinset (a,b)).mpr hab) ha
  · intro a b hab hb
    exact hin a b ((d.mem_segmentFinset (a,b)).mpr hab) hb

/-- Unconditional original-curve-preserving normal collars for any finite
polygonal drawing, including loops and parallel edge occurrences. -/
theorem exists_refined_twoSidedStripData (d : PolygonalDrawing G) :
    Nonempty d.refineSingle.TwoSidedStripData :=
  d.refineSingle.exists_twoSidedStripData (fun _ _ h => d.refined_segment_has_nonhost_endpoint h)

/-- The selected strip data is on the same parametrized original drawing. -/
def originalStripData (d : PolygonalDrawing G) : d.refineSingle.TwoSidedStripData :=
  Classical.choice d.exists_refined_twoSidedStripData

end PlanarHom.MultiGraph.PolygonalDrawing

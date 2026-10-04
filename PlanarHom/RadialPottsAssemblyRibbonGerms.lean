import PlanarHom.OccurrenceKasteleynEdgeCollars
import PlanarHom.PlanarityLRRealizationGermPieces

/-!
# Uniform endpoint germs of the actual polygonal bands

The normal assignment is only a function on finitely many chain vertices. No
regularity assumption about it is needed: the concrete polygonal interpolation
proves one common initial interval simultaneously for every transverse height.
-/
noncomputable section
open Classical Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal.Chain
open MultiGraph
variable {U : Set Plane} {x y : Plane}

/-- The first piece of the actual band is a simultaneous fan of literal rays. -/
theorem vertexBand_uniform_source (p : Chain U x y) (hn : p.length ≠ 0)
    (f : Plane → Plane) (hfx : f x = x) :
    ∃ z ε k, (x,z) ∈ p.segments ∧ 0 < ε ∧ 0 < k ∧
      ∀ t : I, (t : ℝ) ≤ ε → ∀ s : I,
        p.vertexBand f (t,s) = x+(k*(t : ℝ)) • (z-x+(s : ℝ) • (f z-z)) := by
  cases p with
  | nil => exact (hn rfl).elim
  | @cons x z y h p =>
    cases p with
    | nil z hz =>
      refine ⟨y,1,1,by simp [segments],by norm_num,by norm_num,?_⟩
      intro t ht s
      change AffineMap.lineMap x y (t : ℝ)+(s : ℝ) •
        (AffineMap.lineMap (f x) (f y) (t : ℝ)-AffineMap.lineMap x y (t : ℝ)) = _
      rw [hfx]
      simp only [AffineMap.lineMap_apply_module]
      module
    | @cons z w y h' q =>
      refine ⟨z,1/2,2,by simp [segments],by norm_num,by norm_num,?_⟩
      intro t ht s
      simp only [vertexBand,ContinuousMap.coe_mk,strictPath,mapVertices,Path.trans_apply,dif_pos ht]
      change AffineMap.lineMap x z (2*(t : ℝ))+(s : ℝ) •
        (AffineMap.lineMap (f x) (f z) (2*(t : ℝ))-AffineMap.lineMap x z (2*(t : ℝ))) = _
      rw [hfx]
      simp only [AffineMap.lineMap_apply_module]
      module

/-- Exact right-half compatibility, shared by all transverse coordinates. -/
theorem vertexBand_right_half {z w : Plane}
    (h : [x -[ℝ] z] ⊆ U) (h' : [z -[ℝ] w] ⊆ U) (q : Chain U w y)
    (f : Plane → Plane) (t s : I) :
    (Chain.cons h (Chain.cons h' q)).vertexBand f (PlaneDrawing.halfParameter true t,s) =
      (Chain.cons h' q).vertexBand f (t,s) := by
  simp only [vertexBand,ContinuousMap.coe_mk,strictPath,mapVertices,trans_right_half]

/-- The target germ uses the outgoing direction, with one uniform interval for
all transverse coordinates. This includes chains with arbitrarily many bends. -/
theorem vertexBand_uniform_target (p : Chain U x y) (hn : p.length ≠ 0)
    (f : Plane → Plane) (hfy : f y = y) :
    ∃ z ε k, (z,y) ∈ p.segments ∧ 0 < ε ∧ 0 < k ∧
      ∀ t : I, (t : ℝ) ≤ ε → ∀ s : I,
        p.vertexBand f (unitInterval.symm t,s) =
          y+(k*(t : ℝ)) • (z-y+(s : ℝ) • (f z-z)) := by
  induction p with
  | nil => exact (hn rfl).elim
  | @cons x z y h p ih =>
    cases p with
    | nil z hz =>
      refine ⟨x,1,1,by simp [segments],by norm_num,by norm_num,?_⟩
      intro t ht s
      change AffineMap.lineMap x z (unitInterval.symm t : ℝ)+(s : ℝ) •
        (AffineMap.lineMap (f x) (f z) (unitInterval.symm t : ℝ)-
          AffineMap.lineMap x z (unitInterval.symm t : ℝ)) = _
      rw [hfy]
      simp only [AffineMap.lineMap_apply_module,unitInterval.coe_symm_eq]
      module
    | @cons z w y h' q =>
      obtain ⟨v,ε,k,hv,hε,hk,hform⟩ := ih (by simp [length]) hfy
      refine ⟨v,min (ε/2) (1/2),2*k,List.mem_cons_of_mem _ hv,
        lt_min (half_pos hε) (by norm_num),by positivity,?_⟩
      intro t ht s
      have htε := ht.trans (min_le_left _ _)
      have ht1 := ht.trans (min_le_right _ _)
      let u : I := ⟨2*(t : ℝ),by constructor <;> linarith [t.property.1]⟩
      have heq : unitInterval.symm t = PlaneDrawing.halfParameter true (unitInterval.symm u) := by
        apply Subtype.ext
        simp [unitInterval.coe_symm_eq,PlaneDrawing.halfParameter,u]
        ring
      rw [heq,vertexBand_right_half,hform u (by dsimp [u]; linarith)]
      change y+(k*(2*(t : ℝ))) • _ = y+((2*k)*(t : ℝ)) • _
      congr 2
      ring

end PlanarHom.Polygonal.Chain

namespace PlanarHom.MultiGraph.PolygonalDrawing
open Kasteleyn Polygonal PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
namespace TwoSidedStripData
variable {d : PolygonalDrawing G}

/-- Outgoing parametrization uses `true` at the source and `false` at the target. -/
def outgoingParameter (forward : Bool) (t : I) : I := if forward then t else unitInterval.symm t

/-- The finite, concrete endpoint data extracted from a side ribbon. In
particular, `formula` is proved from polygonal interpolation, rather than an
extra geometric requirement on an abstract embedding. -/
structure EndpointFan (D : d.TwoSidedStripData) (positive : Bool) (a : Dart E) (ray : Plane) where
  tip : Plane
  radius : ℝ
  speed : ℝ
  scale : ℝ
  radius_pos : 0 < radius
  speed_pos : 0 < speed
  scale_pos : 0 < scale
  tip_nonhost : tip ∉ d.hostSet
  piece_mem : (if a.2 then (d.drawing.point (G.dartPair a).1,tip)
    else (tip,d.drawing.point (G.dartPair a).1)) ∈ (d.chain a.1).segments
  tip_direction : tip-d.drawing.point (G.dartPair a).1 = scale • ray
  normal_side : if positive = a.2 then
    0 < cross ray (D.width • D.signedNormal positive tip)
    else cross ray (D.width • D.signedNormal positive tip) < 0
  formula : ∀ t : I, (t : ℝ) ≤ radius → ∀ s : I,
    (D.sideRibbon positive).band a.1 (outgoingParameter a.2 t,s) =
      d.drawing.point (G.dartPair a).1+(speed*(t : ℝ)) •
        (scale • ray+(s : ℝ) • (D.width • D.signedNormal positive tip))

/-- Every original straight dart germ induces a uniform fan on its actual
polygonal ribbon, with the correct orientation at both endpoints. -/
theorem exists_endpointFan (D : d.TwoSidedStripData) (positive : Bool) (a : Dart E) (ray : Plane)
    (h : StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) ray) :
    Nonempty (D.EndpointFan positive a ray) := by
  rcases a with ⟨e,b⟩
  cases b
  · let f : Plane → Plane := fun v => v+D.width • D.signedNormal positive v
    have hfy : f (d.drawing.point (G.dst e)) = d.drawing.point (G.dst e) := by
      simp [f,D.signedNormal_host positive _ ⟨G.dst e,rfl⟩]
    obtain ⟨z,ε,k,hz,hε,hk,hform⟩ :=
      (d.chain e).vertexBand_uniform_target (d.chain_length_ne_zero e) f hfy
    obtain ⟨c,hc,hdir⟩ := d.target_piece_direction e hz rfl ray h
    have hseg : (z,d.drawing.point (G.dst e)) ∈ d.segmentSet := ⟨e,hz⟩
    have hn : z ∉ d.hostSet := (D.free_endpoints _ _ hseg).resolve_right (by simp [hostSet])
    have hcross := D.cross_start _ _ hseg hn
    have hh : cross ray (D.normal z) < 0 := by
      have heq : d.drawing.point (G.dst e)-z = -(c • ray) := by rw [← hdir]; abel
      rw [heq,cross_neg_left,cross_smul_left] at hcross
      nlinarith
    refine ⟨⟨z,ε,k,c,hε,hk,hc,hn,hz,hdir,?_,?_⟩⟩
    · cases positive <;> simp only [signedNormal,Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,
        cross_smul_right,cross_neg_right] <;> nlinarith [D.width_pos]
    · intro t ht s
      change (d.chain e).vertexBand f (unitInterval.symm t,s) = _
      rw [hform t ht,hdir]
      dsimp [f]
      congr 3
      abel_nf
  · let f : Plane → Plane := fun v => v+D.width • D.signedNormal positive v
    have hfx : f (d.drawing.point (G.src e)) = d.drawing.point (G.src e) := by
      simp [f,D.signedNormal_host positive _ ⟨G.src e,rfl⟩]
    obtain ⟨z,ε,k,hz,hε,hk,hform⟩ :=
      (d.chain e).vertexBand_uniform_source (d.chain_length_ne_zero e) f hfx
    obtain ⟨c,hc,hdir⟩ := d.source_piece_direction e hz rfl ray h
    have hseg : (d.drawing.point (G.src e),z) ∈ d.segmentSet := ⟨e,hz⟩
    have hn : z ∉ d.hostSet := (D.free_endpoints _ _ hseg).resolve_left (by simp [hostSet])
    have hcross := D.cross_end _ _ hseg hn
    have hh : 0 < cross ray (D.normal z) := by
      rw [hdir,cross_smul_left] at hcross
      nlinarith
    refine ⟨⟨z,ε,k,c,hε,hk,hc,hn,hz,hdir,?_,?_⟩⟩
    · cases positive <;> simp only [signedNormal,Bool.false_eq_true,if_false,if_true,
        cross_smul_right,cross_neg_right] <;> nlinarith [D.width_pos]
    · intro t ht s
      change (d.chain e).vertexBand f (t,s) = _
      rw [hform t ht,hdir]
      dsimp [f]
      congr 3
      abel_nf

end TwoSidedStripData
end PlanarHom.MultiGraph.PolygonalDrawing

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan
open Kasteleyn Polygonal PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {a : Dart E} {ray : Plane}

/-- The exact outgoing vector at an arbitrary transverse coordinate. -/
def direction (F : D.EndpointFan positive a ray) (s : ℝ) : Plane :=
  F.scale • ray+s • (D.width • D.signedNormal positive F.tip)

/-- The two endpoint directions have the actual transverse-coordinate order. -/
theorem cross_direction (F : D.EndpointFan positive a ray) (s u : ℝ) :
    cross (F.direction s) (F.direction u) =
      F.scale*(u-s)*cross ray (D.width • D.signedNormal positive F.tip) := by
  simp only [direction,cross,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem normal_cross_ne_zero (F : D.EndpointFan positive a ray) :
    cross ray (D.width • D.signedNormal positive F.tip) ≠ 0 := by
  have hh := F.normal_side
  split_ifs at hh with heq
  · exact ne_of_gt hh
  · exact ne_of_lt hh

/-- No outgoing fan vector can vanish, including both closed transverse ends. -/
theorem direction_ne_zero (F : D.EndpointFan positive a ray) (s : ℝ) :
    F.direction s ≠ 0 := by
  intro heq
  have h := congrArg (fun v => cross v (D.width • D.signedNormal positive F.tip)) heq
  simp only [direction,cross_add_left,cross_smul_left,cross_self,mul_zero,add_zero,
    cross_zero_left] at h
  exact F.normal_cross_ne_zero ((mul_eq_zero.mp h).resolve_left (ne_of_gt F.scale_pos))

/-- Strict angular order of any two fan positions, with target reversal and
negative-side reversal explicitly accounted for. -/
theorem direction_order (F : D.EndpointFan positive a ray) {s u : ℝ} (hsu : s < u) :
    if positive = a.2 then 0 < cross (F.direction s) (F.direction u)
      else cross (F.direction s) (F.direction u) < 0 := by
  rw [F.cross_direction]
  have hp : 0 < F.scale*(u-s) := mul_pos F.scale_pos (sub_pos.mpr hsu)
  have hh := F.normal_side
  split_ifs at hh ⊢ with heq
  · exact mul_pos hp hh
  · exact mul_neg_of_pos_of_neg hp hh

/-- Positive radial rescaling, including normalization to a common circle,
preserves the strict order. -/
theorem scaled_direction_order (F : D.EndpointFan positive a ray) {s u l m : ℝ}
    (hsu : s < u) (hl : 0 < l) (hm : 0 < m) :
    if positive = a.2 then 0 < cross (l • F.direction s) (m • F.direction u)
      else cross (l • F.direction s) (m • F.direction u) < 0 := by
  rw [cross_smul_left,cross_smul_right]
  have hh := F.direction_order hsu
  split_ifs at hh ⊢ with heq
  · exact mul_pos hl (mul_pos hm hh)
  · exact mul_neg_of_pos_of_neg hl (mul_neg_of_pos_of_neg hm hh)

/-- The fan vectors vary continuously across the complete transverse interval. -/
theorem continuous_direction (F : D.EndpointFan positive a ray) : Continuous F.direction := by
  unfold direction
  fun_prop

/-- An arbitrary thinning of the transverse interval preserves the same exact
endpoint formula and its already proved common longitudinal cutoff. -/
theorem formula_transverse (F : D.EndpointFan positive a ray) (f : I → I)
    (t : I) (ht : (t : ℝ) ≤ F.radius) (s : I) :
    (D.sideRibbon positive).band a.1 (outgoingParameter a.2 t,f s) =
      d.drawing.point (G.dartPair a).1+(F.speed*(t : ℝ)) • F.direction (f s : ℝ) :=
  F.formula t ht (f s)

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan
open Kasteleyn Polygonal PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {a : Dart E} {ray : Plane}

/-- Every fixed transverse slice has the proved outgoing straight germ. -/
theorem straightGerm (F : D.EndpointFan positive a ray) (s : I) :
    StraightGerm (fun t => (D.sideRibbon positive).band a.1 (outgoingParameter a.2 t,s))
      (d.drawing.point (G.dartPair a).1) (F.direction (s : ℝ)) :=
  ⟨F.radius,F.speed,F.radius_pos,F.speed_pos,fun t ht => F.formula t ht s⟩

/-- Moving each fan point a nonzero distance along its own ray cannot identify
two distinct transverse coordinates. In particular all normalized circle ports
are distinct, with no positive-height or open-endpoint restriction. -/
theorem rescaled_direction_injective (F : D.EndpointFan positive a ray) (l : ℝ → ℝ)
    (hl : ∀ s, l s ≠ 0) : Function.Injective (fun s => l s • F.direction s) := by
  intro s u h
  change l s • F.direction s = l u • F.direction u at h
  have hz : cross (l s • F.direction s) (l u • F.direction u) = 0 := by rw [h,cross_self]
  rw [cross_smul_left,cross_smul_right,F.cross_direction] at hz
  have hh : u-s = 0 := by
    have h1 := (mul_eq_zero.mp hz).resolve_left (hl s)
    have h2 := (mul_eq_zero.mp h1).resolve_left (hl u)
    have h3 := (mul_eq_zero.mp h2).resolve_right F.normal_cross_ne_zero
    exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt F.scale_pos)
  exact (sub_eq_zero.mp hh).symm

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan

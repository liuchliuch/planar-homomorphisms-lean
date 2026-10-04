import PlanarHom.RadialPottsAssemblyRibbonMiddle
import PlanarHom.RadialPottsAssemblyRibbonGerms
import PlanarHom.RadialPottsAssemblyCircleCoordinates

/-!
# Uniform circular clipping of actual polygonal ribbons

Endpoint fans and compact host-relative forbidden rectangles determine a common
positive circle radius. The construction includes both ends of loops and keeps
all closed middle-band boundaries; it does not perform vertex-corner routing.
-/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.MultiGraph.RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Every host removes only its own two short endpoint pieces. The rest of each
closed ribbon, including endpoints at other hosts, avoids that host. -/
theorem band_ne_host_of_cut (R : RibbonDrawing G) (δ : I) (hδ : Inside δ)
    (e : E) (t s : I) (v : V)
    (hsrc : G.src e = v → δ ≤ t) (hdst : G.dst e = v → t ≤ unitInterval.symm δ) :
    R.band e (t,s) ≠ R.point v := by
  intro heq
  by_cases ht0 : t = 0
  · subst t
    rw [R.band_zero] at heq
    have hh := hsrc (R.point_injective heq)
    exact (not_le_of_gt hδ.1) hh
  by_cases ht1 : t = 1
  · subst t
    rw [R.band_one] at heq
    have hh := hdst (R.point_injective heq)
    have hreal : (1 : ℝ) ≤ 1-(δ : ℝ) := hh
    have hpos : (0 : ℝ) < δ := hδ.1
    linarith
  exact R.band_avoids e (t,s) (PlaneDrawing.inside_of_ne_endpoints ht0 ht1) v heq

/-- One common metric clearance outside the endpoint fans incident to each
host. Unlike a global middle-third restriction, this covers all points near an
edge's source when testing against any other host, and analogously at its target. -/
theorem host_relative_uniform_clearance [Finite V] [Finite E] (R : RibbonDrawing G)
    (δ : I) (hδ : Inside δ) (hδhalf : δ < unitInterval.symm δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ e t s v,
      (G.src e = v → δ ≤ t) → (G.dst e = v → t ≤ unitInterval.symm δ) →
      r < dist (R.band e (t,s)) (R.point v) := by
  have hlocal : ∀ v : V, ∃ r : ℝ, 0 < r ∧ ∀ e t s,
      (G.src e = v → δ ≤ t) → (G.dst e = v → t ≤ unitInterval.symm δ) →
      r < dist (R.band e (t,s)) (R.point v) := by
    intro v
    let lo : E → I := fun e => if G.src e = v then δ else 0
    let hi : E → I := fun e => if G.dst e = v then unitInterval.symm δ else 1
    have hlt : ∀ e, lo e < hi e := by
      intro e
      dsimp [lo,hi]
      split_ifs
      · exact hδhalf
      · exact hδ.2
      · change (0 : ℝ) < 1-(δ : ℝ)
        have hh : (δ : ℝ) < 1 := hδ.2
        linarith
      · norm_num
    let S : Set Plane := ⋃ e, Set.range (R.middleBand (lo e) (hi e) (hlt e).le e)
    have hS : IsCompact S := isCompact_iUnion fun e =>
      isCompact_range (R.middleBand (lo e) (hi e) (hlt e).le e).continuous
    have hdis : Disjoint S {R.point v} := by
      apply Set.disjoint_left.mpr
      rintro x hx hxv
      obtain ⟨e,p,hp⟩ := Set.mem_iUnion.mp hx
      have hh : R.middleBand (lo e) (hi e) (hlt e).le e p = R.point v := hp.trans (Set.mem_singleton_iff.mp hxv)
      have hb := middleParameter_bounds (lo e) (hi e) (hlt e).le p.1
      apply R.band_ne_host_of_cut δ hδ e _ p.2 v ?_ ?_ hh
      · intro he
        simpa only [lo,if_pos he] using hb.1
      · intro he
        simpa only [hi,if_pos he] using hb.2
    obtain ⟨r,hr,hsep⟩ := EMetric.exists_pos_forall_lt_edist hS isClosed_singleton hdis
    refine ⟨r,hr,?_⟩
    intro e t s hsrc hdst
    have hlo : lo e ≤ t := by dsimp [lo]; split_ifs with he; exact hsrc he; exact bot_le
    have hhi : t ≤ hi e := by dsimp [hi]; split_ifs with he; exact hdst he; exact le_top
    obtain ⟨u,hu⟩ := middleParameter_surjective_Icc (lo e) (hi e) (hlt e) hlo hhi
    have hh := hsep (R.middleBand (lo e) (hi e) (hlt e).le e (u,s))
      (Set.mem_iUnion.mpr ⟨e,(u,s),rfl⟩) _ (Set.mem_singleton _)
    have hr' := (ENNReal.toReal_lt_toReal (by simp) (edist_ne_top _ _)).mpr hh
    simpa only [middleBand_apply,hu,ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] using hr'
  choose ρ hρ hsep using hlocal
  obtain ⟨r,hr,hle⟩ := PlaneDrawing.finite_positive_lower_bound ρ hρ
  exact ⟨r,hr,fun e t s v hs hd => (hle v).trans_lt (hsep v e t s hs hd)⟩

end PlanarHom.MultiGraph.RibbonDrawing

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan
open Kasteleyn Polygonal PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {a : Dart E} {ray : Plane}

/-- The nonzero fan directions give positive literal radial speed. -/
theorem radialSpeed_pos (F : D.EndpointFan positive a ray) (s : ℝ) :
    0 < F.speed*rayLength (F.direction s) :=
  mul_pos F.speed_pos (rayLength_pos_of_ne_zero (F.direction_ne_zero s))

/-- Exact Euclidean distance on the complete initial fan. -/
theorem formula_rayLength (F : D.EndpointFan positive a ray) (t s : I)
    (ht : (t : ℝ) ≤ F.radius) :
    rayLength ((D.sideRibbon positive).band a.1 (outgoingParameter a.2 t,s)-
      d.drawing.point (G.dartPair a).1) = (t : ℝ)*(F.speed*rayLength (F.direction (s : ℝ))) := by
  rw [F.formula t ht]
  change rayLength (_+_ • F.direction (s : ℝ)-_) = _
  rw [add_sub_cancel_left,rayLength_smul,abs_of_nonneg (mul_nonneg F.speed_pos.le t.property.1)]
  ring

/-- The explicit source-side parameter cutting each fan ray at one circle. -/
def circleCut (F : D.EndpointFan positive a ray) (τ : C(I,I)) (r : ℝ) (hr : 0 < r)
    (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ))) : C(I,I) where
  toFun s := ⟨r/(F.speed*rayLength (F.direction (τ s : ℝ))),
    (div_pos hr (F.radialSpeed_pos _)).le,(div_lt_one (F.radialSpeed_pos _)).mpr (hsmall s) |>.le⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div continuous_const
    · exact continuous_const.mul (continuous_rayLength.comp
        (F.continuous_direction.comp (continuous_subtype_val.comp τ.continuous)))
    · intro s
      exact ne_of_gt (F.radialSpeed_pos _)

@[simp] theorem circleCut_val (F : D.EndpointFan positive a ray) (τ : C(I,I))
    (r : ℝ) (hr : 0 < r) (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ))) (s : I) :
    (F.circleCut τ r hr hsmall s : ℝ) = r/(F.speed*rayLength (F.direction (τ s : ℝ))) := rfl

theorem circleCut_inside (F : D.EndpointFan positive a ray) (τ : C(I,I))
    (r : ℝ) (hr : 0 < r) (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ))) (s : I) :
    Inside (F.circleCut τ r hr hsmall s) :=
  ⟨div_pos hr (F.radialSpeed_pos _),(div_lt_one (F.radialSpeed_pos _)).mpr (hsmall s)⟩

theorem circleCut_lt (F : D.EndpointFan positive a ray) (τ : C(I,I))
    (r : ℝ) (hr : 0 < r) (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ)))
    (s : I) (δ : ℝ) (hδ : r < δ*(F.speed*rayLength (F.direction (τ s : ℝ)))) :
    (F.circleCut τ r hr hsmall s : ℝ) < δ :=
  (div_lt_iff₀ (F.radialSpeed_pos _)).mpr hδ

/-- The endpoint lies on the actual Euclidean circle, with an exact point
formula usable by the inverse-Cayley corner chart. -/
theorem circleCut_formula (F : D.EndpointFan positive a ray) (τ : C(I,I))
    (r : ℝ) (hr : 0 < r) (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ)))
    (s : I) (hgerm : (F.circleCut τ r hr hsmall s : ℝ) ≤ F.radius) :
    (D.sideRibbon positive).band a.1 (outgoingParameter a.2 (F.circleCut τ r hr hsmall s),τ s) =
      d.drawing.point (G.dartPair a).1+r • circleRay (F.direction (τ s : ℝ)) := by
  rw [F.formula _ hgerm]
  change _+(F.speed*(r/(F.speed*rayLength (F.direction (τ s : ℝ))))) • F.direction (τ s : ℝ) = _
  have hs : F.speed ≠ 0 := ne_of_gt F.speed_pos
  have hl : rayLength (F.direction (τ s : ℝ)) ≠ 0 :=
    ne_of_gt (rayLength_pos_of_ne_zero (F.direction_ne_zero _))
  apply congrArg (fun x => d.drawing.point (G.dartPair a).1+x)
  apply Prod.ext <;> simp only [circleRay,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> field_simp

/-- Past the unique circle cut, the same endpoint fan is strictly outside it. -/
theorem after_circleCut (F : D.EndpointFan positive a ray) (τ : C(I,I))
    (r : ℝ) (hr : 0 < r) (hsmall : ∀ s, r < F.speed*rayLength (F.direction (τ s : ℝ)))
    (t s : I) (ht : (t : ℝ) ≤ F.radius) (hcut : F.circleCut τ r hr hsmall s < t) :
    r < rayLength ((D.sideRibbon positive).band a.1 (outgoingParameter a.2 t,τ s)-
      d.drawing.point (G.dartPair a).1) := by
  rw [F.formula_rayLength t (τ s) ht]
  exact (div_lt_iff₀ (F.radialSpeed_pos _)).mp hcut

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.EndpointFan

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn Polygonal PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane}

/-- One original longitudinal interval works for every dart and every height. -/
theorem exists_uniform_fan_cutoff (F : ∀ a, D.EndpointFan positive a (rays a)) :
    ∃ δ : I, Inside δ ∧ δ < unitInterval.symm δ ∧ ∀ a, (δ : ℝ) ≤ (F a).radius := by
  obtain ⟨ρ,hρ,hle⟩ := PlaneDrawing.finite_positive_lower_bound
    (fun a => (F a).radius) (fun a => (F a).radius_pos)
  let δ : ℝ := min (ρ/2) (1/4)
  have hδ : 0 < δ := lt_min (half_pos hρ) (by norm_num)
  have hδq : δ ≤ 1/4 := min_le_right _ _
  have hδρ : δ ≤ ρ/2 := min_le_left _ _
  refine ⟨⟨δ,hδ.le,by linarith⟩,⟨hδ,by change δ < 1; linarith⟩,?_,?_⟩
  · change δ < 1-δ
    linarith
  · intro a
    have hh := hle a
    change δ ≤ (F a).radius
    linarith

/-- Fully proved circular end cuts for the actual original ribbon. Both
transverse boundary sides are kept; longitudinal interiors lie outside every
vertex disk. This certificate contains no vertex-corner routing assertion. -/
structure CircleClipping (F : ∀ a, D.EndpointFan positive a (rays a)) (τ : C(I,I)) where
  radius : ℝ
  radius_pos : 0 < radius
  left : E → C(I,I)
  right : E → C(I,I)
  left_inside : ∀ e s, Inside (left e s)
  right_inside : ∀ e s, Inside (right e s)
  left_lt_right : ∀ e s, left e s < right e s
  left_formula : ∀ e s, (D.sideRibbon positive).band e (left e s,τ s) =
    d.drawing.point (G.src e)+radius • circleRay ((F (e,true)).direction (τ s : ℝ))
  right_formula : ∀ e s, (D.sideRibbon positive).band e (right e s,τ s) =
    d.drawing.point (G.dst e)+radius • circleRay ((F (e,false)).direction (τ s : ℝ))
  outside : ∀ e t s v, left e s < t → t < right e s →
    radius < rayLength ((D.sideRibbon positive).band e (t,τ s)-d.drawing.point v)
  disks_disjoint : ∀ v w, v ≠ w → Disjoint
    {p : Plane | rayLength (p-d.drawing.point v) ≤ radius}
    {p : Plane | rayLength (p-d.drawing.point w) ≤ radius}

/-- Every finite actual fan family has simultaneous circle cuts. The only
transverse input is a continuous injection, so arbitrary already-selected
positive ribbon narrowings are covered. -/
theorem exists_circleClipping (F : ∀ a, D.EndpointFan positive a (rays a))
    (τ : C(I,I)) (hτ : Function.Injective τ) : Nonempty (CircleClipping F τ) := by
  let R := (D.sideRibbon positive).mapTransverse τ hτ
  obtain ⟨δ,hδ,hδhalf,hδfan⟩ := exists_uniform_fan_cutoff F
  obtain ⟨ρ,hρ,hmargin⟩ := R.host_relative_uniform_clearance δ hδ hδhalf
  let pairs := {p : V × V // p.1 ≠ p.2}
  obtain ⟨κ,hκ,hκsep⟩ := PlaneDrawing.finite_positive_lower_bound
    (fun p : pairs => dist (d.drawing.point p.val.1) (d.drawing.point p.val.2))
    (fun p => dist_pos.mpr (d.drawing.point_injective.ne p.property))
  let r : ℝ := min (ρ/2) (κ/4)
  have hr : 0 < r := lt_min (half_pos hρ) (by positivity)
  have hrρ : r < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hrκ : r ≤ κ/4 := min_le_right _ _
  have hcutoff : ∀ a s, r < (δ : ℝ)*((F a).speed*rayLength ((F a).direction (τ s : ℝ))) := by
    intro a s
    have hm : ρ < dist ((D.sideRibbon positive).band a.1 (outgoingParameter a.2 δ,τ s))
        (d.drawing.point (G.dartPair a).1) := by
      rcases a with ⟨e,b⟩
      cases b
      · exact hmargin e (unitInterval.symm δ) s (G.dst e) (fun _ => hδhalf.le) (fun _ => le_rfl)
      · exact hmargin e δ s (G.src e) (fun _ => le_rfl) (fun _ => hδhalf.le)
    have hn := norm_le_rayLength ((D.sideRibbon positive).band a.1
      (outgoingParameter a.2 δ,τ s)-d.drawing.point (G.dartPair a).1)
    rw [(F a).formula_rayLength δ (τ s) (hδfan a)] at hn
    rw [dist_eq_norm] at hm
    exact hrρ.trans (hm.trans_le hn)
  have hsmall : ∀ a s, r < (F a).speed*rayLength ((F a).direction (τ s : ℝ)) := by
    intro a s
    have hh := hcutoff a s
    have hp := (F a).radialSpeed_pos (τ s : ℝ)
    have hd : (δ : ℝ) < 1 := hδ.2
    nlinarith
  let cut : Dart E → C(I,I) := fun a => (F a).circleCut τ r hr (hsmall a)
  have hcin : ∀ a s, Inside (cut a s) := fun a s => (F a).circleCut_inside τ r hr (hsmall a) s
  have hclt : ∀ a s, cut a s < δ := fun a s =>
    (F a).circleCut_lt τ r hr (hsmall a) s δ (hcutoff a s)
  let left : E → C(I,I) := fun e => cut (e,true)
  let right : E → C(I,I) := fun e =>
    ⟨fun s => unitInterval.symm (cut (e,false) s),unitInterval.continuous_symm.comp (cut (e,false)).continuous⟩
  have hleft : ∀ e s, Inside (left e s) := fun e s => hcin (e,true) s
  have hright : ∀ e s, Inside (right e s) := by
    intro e s
    have hh := hcin (e,false) s
    change 0 < unitInterval.symm (cut (e,false) s) ∧ unitInterval.symm (cut (e,false) s) < 1
    constructor
    · change (0 : ℝ) < 1-(cut (e,false) s : ℝ)
      have ht : (cut (e,false) s : ℝ) < 1 := hh.2
      linarith
    · change 1-(cut (e,false) s : ℝ) < 1
      have ht : (0 : ℝ) < cut (e,false) s := hh.1
      linarith
  have horder : ∀ e s, left e s < right e s := by
    intro e s
    exact (hclt (e,true) s).trans (hδhalf.trans (unitInterval.strictAnti_symm (hclt (e,false) s)))
  refine ⟨⟨r,hr,left,right,hleft,hright,horder,?_,?_,?_,?_⟩⟩
  · intro e s
    exact (F (e,true)).circleCut_formula τ r hr (hsmall (e,true)) s
      ((show (cut (e,true) s : ℝ) ≤ δ from (hclt (e,true) s).le).trans (hδfan (e,true)))
  · intro e s
    exact (F (e,false)).circleCut_formula τ r hr (hsmall (e,false)) s
      ((show (cut (e,false) s : ℝ) ≤ δ from (hclt (e,false) s).le).trans (hδfan (e,false)))
  · intro e t s v hlt htr
    by_cases hs : G.src e = v ∧ t < δ
    · rw [← hs.1]
      exact (F (e,true)).after_circleCut τ r hr (hsmall (e,true)) t s
        ((show (t : ℝ) ≤ δ from hs.2.le).trans (hδfan (e,true))) hlt
    by_cases hd : G.dst e = v ∧ unitInterval.symm δ < t
    · rw [← hd.1]
      have htδ : unitInterval.symm t < δ := by
        simpa only [unitInterval.symm_symm] using unitInterval.strictAnti_symm hd.2
      have hct : cut (e,false) s < unitInterval.symm t := by
        have hh := unitInterval.strictAnti_symm htr
        simpa only [right,ContinuousMap.coe_mk,unitInterval.symm_symm] using hh
      have hh := (F (e,false)).after_circleCut τ r hr (hsmall (e,false))
        (unitInterval.symm t) s ((show (unitInterval.symm t : ℝ) ≤ δ from htδ.le).trans (hδfan (e,false))) hct
      simpa only [outgoingParameter,Bool.false_eq_true,if_false,unitInterval.symm_symm] using hh
    · have hm := hmargin e t s v (fun he => not_lt.mp (fun h => hs ⟨he,h⟩))
        (fun he => not_lt.mp (fun h => hd ⟨he,h⟩))
      have hn := norm_le_rayLength ((D.sideRibbon positive).band e (t,τ s)-d.drawing.point v)
      rw [dist_eq_norm] at hm
      exact hrρ.trans (hm.trans_le hn)
  · intro v w hvw
    apply Set.disjoint_left.mpr
    intro p hpv hpw
    have hv : dist p (d.drawing.point v) ≤ r := (norm_le_rayLength _).trans hpv
    have hw : dist p (d.drawing.point w) ≤ r := (norm_le_rayLength _).trans hpw
    have hk := hκsep ⟨(v,w),hvw⟩
    have ht := dist_triangle (d.drawing.point v) p (d.drawing.point w)
    rw [dist_comm (d.drawing.point v) p] at ht
    dsimp at hk
    linarith

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)} {τ : C(I,I)}

/-- The actual closed band between the two circles, with the original
occurrence identity retained. It is ready for composition with a square tile. -/
def band (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) : C(I × I,Plane) :=
  ((D.sideRibbon positive).mapTransverse τ hτ).clippedBand (C.left e) (C.right e)
    (fun s => (C.left_lt_right e s).le) e

@[simp] theorem band_apply (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (p : I × I) :
    C.band hτ e p = (D.sideRibbon positive).band e
      (RibbonDrawing.middleParameter (C.left e p.2) (C.right e p.2)
        (C.left_lt_right e p.2).le p.1,τ p.2) := rfl

/-- Each complete closed circle-clipped rectangle is an embedding. -/
theorem band_isClosedEmbedding (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) :
    Topology.IsClosedEmbedding (C.band hτ e) :=
  ((D.sideRibbon positive).mapTransverse τ hτ).clippedBand_isClosedEmbedding
    (C.left e) (C.right e) (C.left_lt_right e) (C.left_inside e) (C.right_inside e) e

/-- Distinct occurrences have disjoint closed circle-clipped bands, including
every circle boundary port. This also covers parallel edges and loop occurrences. -/
theorem bands_disjoint (C : CircleClipping F τ) (hτ : Function.Injective τ)
    {e f : E} (hef : e ≠ f) : Disjoint (Set.range (C.band hτ e)) (Set.range (C.band hτ f)) :=
  ((D.sideRibbon positive).mapTransverse τ hτ).clippedBand_disjoint_of_cuts
    (C.left e) (C.right e) (C.left f) (C.right f)
    (fun s => (C.left_lt_right e s).le) (fun s => (C.left_lt_right f s).le)
    (C.left_inside e) (C.right_inside e) (C.left_inside f) (C.right_inside f) hef

@[simp] theorem band_zero (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) (s : I) :
    C.band hτ e (0,s) = d.drawing.point (G.src e)+
      C.radius • circleRay ((F (e,true)).direction (τ s : ℝ)) := by
  rw [band_apply,RibbonDrawing.middleParameter_zero,C.left_formula]

@[simp] theorem band_one (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) (s : I) :
    C.band hτ e (1,s) = d.drawing.point (G.dst e)+
      C.radius • circleRay ((F (e,false)).direction (τ s : ℝ)) := by
  rw [band_apply,RibbonDrawing.middleParameter_one,C.right_formula]

/-- Every open longitudinal slice, including both transverse boundary sides,
lies strictly outside every old vertex circle. -/
theorem band_outside (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (p : I × I) (hp : Inside p.1) (v : V) :
    C.radius < rayLength (C.band hτ e p-d.drawing.point v) := by
  rw [band_apply]
  apply C.outside
  · have hh := RibbonDrawing.middleParameter_strictMono (C.left e p.2) (C.right e p.2)
      (C.left_lt_right e p.2) (show (0 : I) < p.1 from hp.1)
    simpa only [RibbonDrawing.middleParameter_zero] using hh
  · have hh := RibbonDrawing.middleParameter_strictMono (C.left e p.2) (C.right e p.2)
      (C.left_lt_right e p.2) (show p.1 < (1 : I) from hp.2)
    simpa only [RibbonDrawing.middleParameter_one] using hh

/-- The whole source cut lies exactly on its Euclidean circle. -/
theorem band_zero_circle (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) (s : I) :
    rayLength (C.band hτ e (0,s)-d.drawing.point (G.src e)) = C.radius := by
  rw [C.band_zero,add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    circleRay_rayLength ((F (e,true)).direction_ne_zero _),mul_one]

/-- The whole target cut lies exactly on its Euclidean circle. -/
theorem band_one_circle (C : CircleClipping F τ) (hτ : Function.Injective τ) (e : E) (s : I) :
    rayLength (C.band hτ e (1,s)-d.drawing.point (G.dst e)) = C.radius := by
  rw [C.band_one,add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    circleRay_rayLength ((F (e,false)).direction_ne_zero _),mul_one]

/-- A tile point strictly inside the square's longitudinal coordinate is
separated from any corner curve contained in a closed vertex disk. -/
theorem band_ne_diskPoint (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (p : I × I) (hp : Inside p.1) (v : V) (q : Plane)
    (hq : rayLength (q-d.drawing.point v) ≤ C.radius) : C.band hτ e p ≠ q := by
  intro heq
  have hh := C.band_outside hτ e p hp v
  rw [heq] at hh
  exact (not_lt_of_ge hq) hh

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)} {τ : C(I,I)}

theorem band_zero_outside_other (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (s : I) (v : V) (hv : G.src e ≠ v) :
    C.radius < rayLength (C.band hτ e (0,s)-d.drawing.point v) := by
  apply lt_of_not_ge
  intro hh
  exact Set.disjoint_left.mp (C.disks_disjoint (G.src e) v hv)
    (by exact (C.band_zero_circle hτ e s).le) hh

theorem band_one_outside_other (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (s : I) (v : V) (hv : G.dst e ≠ v) :
    C.radius < rayLength (C.band hτ e (1,s)-d.drawing.point v) := by
  apply lt_of_not_ge
  intro hh
  exact Set.disjoint_left.mp (C.disks_disjoint (G.dst e) v hv)
    (by exact (C.band_one_circle hτ e s).le) hh

/-- The complete closed band stays outside every open vertex disk. -/
theorem band_radius_le (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (p : I × I) (v : V) :
    C.radius ≤ rayLength (C.band hτ e p-d.drawing.point v) := by
  rcases p with ⟨t,s⟩
  by_cases ht0 : t = 0
  · subst t
    by_cases hv : G.src e = v
    · rw [← hv,C.band_zero_circle]
    · exact (C.band_zero_outside_other hτ e s v hv).le
  by_cases ht1 : t = 1
  · subst t
    by_cases hv : G.dst e = v
    · rw [← hv,C.band_one_circle]
    · exact (C.band_one_outside_other hτ e s v hv).le
  exact (C.band_outside hτ e (t,s) (PlaneDrawing.inside_of_ne_endpoints ht0 ht1) v).le

/-- Exact classification of all circle contacts, including the two distinct
cuts of a loop at the same old vertex. No other band point touches any circle. -/
theorem band_on_circle_iff (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (p : I × I) (v : V) :
    rayLength (C.band hτ e p-d.drawing.point v) = C.radius ↔
      (p.1 = 0 ∧ G.src e = v) ∨ (p.1 = 1 ∧ G.dst e = v) := by
  rcases p with ⟨t,s⟩
  constructor
  · intro h
    by_cases ht0 : t = 0
    · subst t
      by_cases hv : G.src e = v
      · exact Or.inl ⟨rfl,hv⟩
      · exact ((ne_of_gt (C.band_zero_outside_other hτ e s v hv)) h).elim
    by_cases ht1 : t = 1
    · subst t
      by_cases hv : G.dst e = v
      · exact Or.inr ⟨rfl,hv⟩
      · exact ((ne_of_gt (C.band_one_outside_other hτ e s v hv)) h).elim
    exact ((ne_of_gt (C.band_outside hτ e (t,s)
      (PlaneDrawing.inside_of_ne_endpoints ht0 ht1) v)) h).elim
  · rintro (⟨ht,hv⟩ | ⟨ht,hv⟩)
    · change t = 0 at ht
      subst t
      rw [← hv,C.band_zero_circle]
    · change t = 1 at ht
      subst t
      rw [← hv,C.band_one_circle]

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G}

/-- End-to-end interface from the actual original dart germs. A single derived
fan family works for every later injective transverse narrowing. -/
theorem exists_fans_and_circleClippings (D : d.TwoSidedStripData) (positive : Bool)
    (rays : Dart E → Plane)
    (hgerm : ∀ a, StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a)) :
    ∃ F : ∀ a, D.EndpointFan positive a (rays a), ∀ τ : C(I,I),
      Function.Injective τ → Nonempty (CircleClipping F τ) := by
  let F := fun a => Classical.choice (D.exists_endpointFan positive a (rays a) (hgerm a))
  exact ⟨F,fun τ hτ => exists_circleClipping F τ hτ⟩

/-- The exact `s ↦ η*s` narrowing used to preserve computed rotation gaps is
admissible for all positive `η ≤ 1`. -/
theorem exists_narrow_circleClipping {D : d.TwoSidedStripData} {positive : Bool}
    {rays : Dart E → Plane} (F : ∀ a, D.EndpointFan positive a (rays a)) (η : I) (hη : 0 < η) :
    Nonempty (CircleClipping F (RibbonDrawing.middleParameter 0 η hη.le)) :=
  exists_circleClipping F _ (RibbonDrawing.middleParameter_strictMono 0 η hη).injective

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

namespace PlanarHom.MultiGraph.PolygonalDrawing
open Kasteleyn PlanarityLRRealization TwoSidedStripData
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- No strip certificate is an extra input: obtain it by the proved
curve-preserving refinement of any actual finite polygonal drawing. -/
theorem exists_refined_fans_and_circleClippings (d : PolygonalDrawing G)
    (positive : Bool) (rays : Dart E → Plane)
    (hgerm : ∀ a, StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a)) :
    ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ F : ∀ a, D.EndpointFan positive a (rays a), ∀ τ : C(I,I),
        Function.Injective τ → Nonempty (CircleClipping F τ) := by
  obtain ⟨D⟩ := d.exists_refined_twoSidedStripData
  obtain ⟨F,hF⟩ := D.exists_fans_and_circleClippings positive rays hgerm
  exact ⟨D,F,hF⟩

end PlanarHom.MultiGraph.PolygonalDrawing

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)} {τ : C(I,I)}

/-- Single recovery theorem for an occurrence and both closed-square coordinates. -/
theorem band_joint_injective (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e f : E) (p q : I × I) (h : C.band hτ e p = C.band hτ f q) : e = f ∧ p = q := by
  by_cases hef : e = f
  · subst f
    exact ⟨rfl,(C.band_isClosedEmbedding hτ e).injective h⟩
  · exact (Set.disjoint_left.mp (C.bands_disjoint hτ hef) ⟨p,rfl⟩ ⟨q,h.symm⟩).elim

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

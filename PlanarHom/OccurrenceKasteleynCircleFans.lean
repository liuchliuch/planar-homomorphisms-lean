import PlanarHom.FiniteCircleFanGap

/-! NEW simultaneous local fan geometry extracted from the recovered clipping.
This constructs an omitted circle point for every actual host, so local port
intervals can be linearized without assuming a rotation or gap certificate. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn Polygonal RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))

/-- The actual normalized endpoint fan, extended to all real transverse values. -/
def normalizedFan (a : Dart E) : C(ℝ,Plane) where
  toFun s := circleRay ((F a).direction s)
  continuous_toFun := by
    have hc := continuous_rayLength.comp (F a).continuous_direction
    have hn : ∀ s, rayLength ((F a).direction s)≠0 :=
      fun s => (rayLength_pos_of_ne_zero ((F a).direction_ne_zero s)).ne'
    exact ((F a).continuous_direction.fst.div hc hn).prodMk ((F a).continuous_direction.snd.div hc hn)

theorem normalizedFan_injective (a : Dart E) : Function.Injective (normalizedFan F a) := by
  have h := (F a).rescaled_direction_injective
    (fun s => (rayLength ((F a).direction s))⁻¹)
    (fun s => inv_ne_zero (rayLength_pos_of_ne_zero ((F a).direction_ne_zero s)).ne')
  convert h using 1
  funext s
  apply Prod.ext <;> simp [normalizedFan,circleRay,div_eq_mul_inv,mul_comm]

theorem normalizedFan_circle (a : Dart E) (s : ℝ) : rayLength (normalizedFan F a s)=1 :=
  circleRay_rayLength ((F a).direction_ne_zero s)

namespace CircleClipping
variable {F}
variable (C : CircleClipping F (ContinuousMap.id I))

/-- Literal source/target circle point at the chosen transverse position. -/
def port (a : Dart E) (s : I) : Plane :=
  C.band Function.injective_id a.1 (if a.2 then 0 else 1,s)

theorem port_formula (a : Dart E) (s : I) :
    C.port a s = d.drawing.point (G.dartPair a).1 + C.radius • normalizedFan F a s := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [port,MultiGraph.dartPair,C.band_zero,C.band_one,normalizedFan]

/-- Every endpoint occurrence and every closed transverse coordinate remain
separate, including the two endpoints of the same loop occurrence. -/
theorem port_injective {a b : Dart E} {s t : I} (h : C.port a s=C.port b t) : a=b ∧ s=t := by
  rcases a with ⟨e,be⟩
  rcases b with ⟨f,bf⟩
  by_cases hef : e=f
  · subst f
    have hp := (C.band_isClosedEmbedding Function.injective_id e).injective h
    have hs : s=t := congrArg Prod.snd hp
    have ht := congrArg Prod.fst hp
    cases be <;> cases bf
    · exact ⟨rfl,hs⟩
    · norm_num at ht
    · norm_num at ht
    · exact ⟨rfl,hs⟩
  · exact False.elim (Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hef)
      ⟨(if be then 0 else 1,s),rfl⟩ ⟨(if bf then 0 else 1,t),h.symm⟩)

include C in
/-- At one host, distinct dart fans give genuinely disjoint normalized circle
intervals, with no assumed angular order. -/
theorem normalizedFans_disjoint (v : V) {a b : Dart E}
    (ha : (G.dartPair a).1=v) (hb : (G.dartPair b).1=v) (hab : a≠b) :
    Disjoint (normalizedFan F a '' Set.Icc 0 1) (normalizedFan F b '' Set.Icc 0 1) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,hs,hsp⟩ ⟨t,ht,htp⟩
  have hport : C.port a ⟨s,hs⟩=C.port b ⟨t,ht⟩ := by
    rw [C.port_formula,C.port_formula,ha,hb]
    exact congrArg (fun q : Plane => d.drawing.point v+C.radius • q) (hsp.trans htp.symm)
  exact hab (C.port_injective hport).1

include C in
/-- A simultaneous actual gap outside every incident closed fan is derived at
each host. This is the cut needed for geometric cyclic rows and collar corners. -/
theorem exists_host_fan_gap (v : V) :
    ∃ p : Plane, rayLength p=1 ∧
      ∀ a : Dart E, (G.dartPair a).1=v → ∀ s : I, normalizedFan F a s≠p := by
  classical
  let A := {a : Dart E // (G.dartPair a).1=v}
  obtain ⟨p,hp,hgap⟩ := FiniteCircleFanGap.exists_gap
    (fun a : A => normalizedFan F a.val)
    (fun a => normalizedFan_injective F a.val)
    (fun a => normalizedFan_circle F a.val)
    (fun a b hab => C.normalizedFans_disjoint v a.property b.property
      (fun h => hab (Subtype.ext h)))
  refine ⟨p,hp,?_⟩
  intro a ha s hs
  exact hgap ⟨a,ha⟩ ⟨(s:ℝ),s.property,hs⟩

end CircleClipping
end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

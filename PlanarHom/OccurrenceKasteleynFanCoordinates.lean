import PlanarHom.OccurrenceKasteleynContourSides
import PlanarHom.PlanarityLRReversedSlots

/-! NEW exact inverse coordinates for finite lanes in actual closed host fans.
The coordinate exists by the proved whole-fan interval image, and is unique.
Crossing a band reverses the actual chart-height order at its other endpoint. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn Polygonal RadialPottsAssemblyGeometry PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}

namespace HostFanChart
variable {v : V} (H : HostFanChart F v)

/-- The unique actual transverse coordinate at any prescribed fan height. -/
def parameterAt (a : HostDart G v) (x : ℝ) (hx : x∈Icc (H.lower a) (H.upper a)) : I :=
  Classical.choose (show x∈Set.range (H.height a) from (H.height_range a).symm ▸ hx)

@[simp] theorem height_parameterAt (a : HostDart G v) (x : ℝ)
    (hx : x∈Icc (H.lower a) (H.upper a)) : H.height a (H.parameterAt a x hx)=x :=
  Classical.choose_spec (show x∈Set.range (H.height a) from (H.height_range a).symm ▸ hx)

theorem parameterAt_inside (a : HostDart G v) (x : ℝ)
    (hx : x∈Ioo (H.lower a) (H.upper a)) :
    Inside (H.parameterAt a x ⟨hx.1.le,hx.2.le⟩) := by
  let s := H.parameterAt a x ⟨hx.1.le,hx.2.le⟩
  have hs : H.height a s=x := H.height_parameterAt a x _
  have h0 : s≠0 := by
    intro he
    rw [he] at hs
    have hh : H.height a 0=H.lower a ∨ H.height a 0=H.upper a := by
      by_cases h : H.height a 0≤H.height a 1
      · exact Or.inl (min_eq_left h).symm
      · exact Or.inr (max_eq_left (le_of_not_ge h)).symm
    rcases hh with hh | hh <;> rw [hh] at hs <;> linarith [hx.1,hx.2]
  have h1 : s≠1 := by
    intro he
    rw [he] at hs
    have hh : H.height a 1=H.lower a ∨ H.height a 1=H.upper a := by
      by_cases h : H.height a 0≤H.height a 1
      · exact Or.inr (max_eq_right h).symm
      · exact Or.inl (min_eq_right (le_of_not_ge h)).symm
    rcases hh with hh | hh <;> rw [hh] at hs <;> linarith [hx.1,hx.2]
  exact ⟨lt_of_le_of_ne s.2.1 (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne s.2.2 (fun h => h1 (Subtype.ext h))⟩

def slotParameter (a : HostDart G v) (n : ℕ) (i : Fin n) : I :=
  H.parameterAt a (reversedSlot (H.lower a) (H.upper a) n i)
    ⟨(reversedSlot_bounds (H.lower_lt_upper a) n i).1.le,
      (reversedSlot_bounds (H.lower_lt_upper a) n i).2.le⟩

@[simp] theorem height_slotParameter (a : HostDart G v) (n : ℕ) (i : Fin n) :
    H.height a (H.slotParameter a n i)=reversedSlot (H.lower a) (H.upper a) n i :=
  H.height_parameterAt a _ _

theorem slotParameter_inside (a : HostDart G v) (n : ℕ) (i : Fin n) :
    Inside (H.slotParameter a n i) :=
  H.parameterAt_inside a _ (reversedSlot_bounds (H.lower_lt_upper a) n i)

theorem slotParameter_injective (a : HostDart G v) (n : ℕ) :
    Function.Injective (H.slotParameter a n) := by
  intro i j h
  apply (reversedSlot_strictAnti (H.lower_lt_upper a) n).injective
  simpa only [H.height_slotParameter] using congrArg (H.height a) h

/-- The proved opposite fan orientations force strict order reversal across
each actual occurrence, for all transverse coordinates, including loop ends. -/
theorem reverse_height_lt_iff {w : V} (K : HostFanChart F w)
    (a : HostDart G v) (b : HostDart G w) (hb : b.val=(a.val.1,!a.val.2)) (s t : I) :
    K.height b s<K.height b t ↔ H.height a t<H.height a s := by
  have ha := H.height_orientation a
  have hh := K.height_orientation b
  have hb2 : b.val.2=(!a.val.2) := congrArg Prod.snd hb
  by_cases hp : positive=a.val.2
  · have hp' : positive≠b.val.2 := by rw [hp,hb2]; cases a.val.2 <;> decide
    rw [if_pos hp] at ha
    rw [if_neg hp'] at hh
    exact hh.lt_iff_gt.trans ha.lt_iff_lt.symm
  · have hp' : positive=b.val.2 := by
      rw [hb2]
      exact Bool.eq_not_iff.mpr hp
    rw [if_neg hp] at ha
    rw [if_pos hp'] at hh
    exact hh.lt_iff_lt.trans ha.lt_iff_gt.symm

/-- Finite lanes returned in reversed slots become increasing at the other
endpoint, exactly as required by the rooted contour scan. -/
theorem opposite_slot_heights_strictMono {w : V} (K : HostFanChart F w)
    (a : HostDart G v) (b : HostDart G w) (hb : b.val=(a.val.1,!a.val.2)) (n : ℕ) :
    StrictMono (fun i => K.height b (H.slotParameter a n i)) := by
  intro i j hij
  apply (H.reverse_height_lt_iff K a b hb _ _).mpr
  simpa only [H.height_slotParameter] using reversedSlot_strictAnti (H.lower_lt_upper a) n hij

end HostFanChart
end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

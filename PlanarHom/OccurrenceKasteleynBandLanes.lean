import PlanarHom.OccurrenceKasteleynHostDiskRouting

/-! NEW actual finite parallel lanes in clipped occurrence bands. The local
disk routes and the band lanes share exactly their named parent-fan slot. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

/-- Traverse the original band at one fixed arbitrary transverse coordinate. -/
def bandLane (a : Dart E) (s : I) : C(I,Plane) where
  toFun t := C.band Function.injective_id a.1 (outgoingParameter a.2 t,s)
  continuous_toFun := (C.band Function.injective_id a.1).continuous.comp (by
    cases a.2 <;> simp only [outgoingParameter,Bool.false_eq_true,if_false,if_true] <;> fun_prop)

@[simp] theorem bandLane_zero (a : Dart E) (s : I) : C.bandLane a s 0=C.port a s := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [bandLane,port,outgoingParameter]

@[simp] theorem bandLane_one (a : Dart E) (s : I) : C.bandLane a s 1=C.port (a.1,!a.2) s := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [bandLane,port,outgoingParameter]

theorem bandLane_injective (a : Dart E) (s : I) : Function.Injective (C.bandLane a s) := by
  intro t u h
  have ht := congrArg Prod.fst ((C.band_isClosedEmbedding Function.injective_id a.1).injective h)
  cases hb : a.2 <;> simpa only [outgoingParameter,hb,Bool.false_eq_true,if_false,if_true,
    unitInterval.symm_inj] using ht

theorem bandLanes_disjoint {a b : Dart E} {s t : I} (h : a.1≠b.1 ∨ s≠t) :
    Disjoint (Set.range (C.bandLane a s)) (Set.range (C.bandLane b t)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,hu⟩ ⟨v,hv⟩
  have he := hu.trans hv.symm
  by_cases hab : a.1=b.1
  · have hp : C.band Function.injective_id a.1 (outgoingParameter a.2 u,s)=
        C.band Function.injective_id a.1 (outgoingParameter b.2 v,t) := by
      simpa only [bandLane,ContinuousMap.coe_mk,← hab] using he
    have hst := congrArg Prod.snd ((C.band_isClosedEmbedding Function.injective_id a.1).injective hp)
    exact h.elim (fun hn => hn hab) (fun hn => hn hst)
  · exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hab)
      ⟨(outgoingParameter a.2 u,s),rfl⟩ ⟨(outgoingParameter b.2 v,t),he.symm⟩

theorem bandLane_mem_band (a : Dart E) (s t : I) :
    C.bandLane a s t∈Set.range (C.band Function.injective_id a.1) :=
  ⟨(outgoingParameter a.2 t,s),rfl⟩

theorem bandLane_disjoint_band {a : Dart E} {e : E} (hae : a.1≠e) (s : I) :
    Disjoint (Set.range (C.bandLane a s)) (Set.range (C.band Function.injective_id e)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨t,rfl⟩ hx
  exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hae) (C.bandLane_mem_band a s t) hx

theorem bandLane_outside (a : Dart E) (s t : I) (ht : Inside t) (v : V) :
    C.radius<rayLength (C.bandLane a s t-d.drawing.point v) := by
  apply C.band_outside Function.injective_id a.1 (outgoingParameter a.2 t,s) _ v
  cases hb : a.2
  · change Inside (unitInterval.symm t)
    constructor <;> change _ < _ <;> simp only [unitInterval.coe_symm_eq] <;> linarith [ht.1,ht.2]
  · exact ht

def bandLanePath (a : Dart E) (s : I) : Path (C.port a s) (C.port (a.1,!a.2) s) where
  toContinuousMap := C.bandLane a s
  source' := C.bandLane_zero a s
  target' := C.bandLane_one a s

variable {v : V} (H : HostFanChart F v)

def rootwardDiskPath (p : HostDart G v) (n : ℕ) (input : Fin n → HostDart G v × I) (i : Fin n) :
    Path (C.port (input i).1.val (input i).2) (C.port p.val (H.slotParameter p n i)) where
  toContinuousMap := C.rootwardDiskLane H p n input i
  source' := C.rootwardDiskLane_zero H p n input i
  target' := C.rootwardDiskLane_one H p n input i

/-- One actual rootward step: cross the host disk, then its parent band. -/
def rootwardStep (p : HostDart G v) (n : ℕ) (input : Fin n → HostDart G v × I) (i : Fin n) :
    Path (C.port (input i).1.val (input i).2) (C.port (p.val.1,!p.val.2) (H.slotParameter p n i)) :=
  (C.rootwardDiskPath H p n input i).trans (C.bandLanePath p.val (H.slotParameter p n i))

theorem port_notMem_other_band {a : Dart E} {e : E} (hae : a.1≠e) (s : I) :
    C.port a s∉Set.range (C.band Function.injective_id e) := by
  intro hh
  exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hae)
    ⟨(if a.2 then 0 else 1,s),rfl⟩ hh

/-- All disk/band intersections are the designated seam. In particular there
are no cross-lane intersections and no hidden second contact at a loop end. -/
theorem rootwardDiskLane_bandLane_intersection (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I)
    (hout : ∀ i, (input i).1.val.1≠p.val.1) (i j : Fin n) (s t : I)
    (he : C.rootwardDiskLane H p n input i s=C.bandLane p.val (H.slotParameter p n j) t) :
    s=1 ∧ t=0 ∧ i=j := by
  have hne : H.height (input i).1 (input i).2≠reversedSlot (H.lower p) (H.upper p) n i :=
    outside_ne_reversedSlot (H.lower_lt_upper p) n i (height_outside_parent H
      (fun h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) _)
  have hs : s=1 := by
    by_cases hs0 : s=0
    · rw [hs0,C.rootwardDiskLane_zero] at he
      exact False.elim (C.port_notMem_other_band (hout i) _ (he ▸ C.bandLane_mem_band _ _ _))
    by_contra hs1
    exact C.hostDiskArc_interior_notMem_band H hne s
      (PlaneDrawing.inside_of_ne_endpoints hs0 hs1) p.val.1 (he ▸ C.bandLane_mem_band _ _ _)
  rw [hs,C.rootwardDiskLane_one] at he
  have hp := (C.band_isClosedEmbedding Function.injective_id p.val.1).injective he
  have hij : i=j := H.slotParameter_injective p n (congrArg Prod.snd hp)
  subst j
  have ht : t=0 := (C.bandLane_injective p.val (H.slotParameter p n i))
    (he.symm.trans (C.bandLane_zero _ _).symm)
  exact ⟨hs,ht,rfl⟩

theorem rootwardStep_injective (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1) (i : Fin n) :
    Function.Injective (C.rootwardStep H p n input i) := by
  apply Polygonal.path_trans_injective
    (C.rootwardDiskPath H p n input i) (C.bandLanePath p.val (H.slotParameter p n i))
  · exact C.rootwardDiskLane_injective H p n input
      (fun i h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) i
  · exact C.bandLane_injective _ _
  · rintro x ⟨s,hs⟩ ⟨t,ht⟩
    have hh := C.rootwardDiskLane_bandLane_intersection H p n input hout i i s t (hs.trans ht.symm)
    rw [hh.1] at hs
    exact hs.symm.trans (C.rootwardDiskLane_one H p n input i)

theorem rootwardSteps_disjoint (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (horder : ∀ i j, i<j → AfterGapOrder (H.lower p) (H.upper p)
      (H.height (input i).1 (input i).2) (H.height (input j).1 (input j).2))
    (i j : Fin n) (hne : i≠j) :
    Disjoint (Set.range (C.rootwardStep H p n input i)) (Set.range (C.rootwardStep H p n input j)) := by
  change Disjoint (Set.range ((C.rootwardDiskPath H p n input i).trans _))
    (Set.range ((C.rootwardDiskPath H p n input j).trans _))
  rw [Path.trans_range,Path.trans_range]
  apply Set.disjoint_left.mpr
  rintro x (⟨s,hs⟩ | ⟨s,hs⟩) (⟨t,ht⟩ | ⟨t,ht⟩)
  · exact Set.disjoint_left.mp (C.rootwardDiskLanes_disjoint H p n input
      (fun i h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) horder i j hne) ⟨s,hs⟩ ⟨t,ht⟩
  · exact hne (C.rootwardDiskLane_bandLane_intersection H p n input hout i j s t (hs.trans ht.symm)).2.2
  · exact hne (C.rootwardDiskLane_bandLane_intersection H p n input hout j i t s (ht.trans hs.symm)).2.2.symm
  · exact Set.disjoint_left.mp (C.bandLanes_disjoint
      (Or.inr ((H.slotParameter_injective p n).ne hne))) ⟨s,hs⟩ ⟨t,ht⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

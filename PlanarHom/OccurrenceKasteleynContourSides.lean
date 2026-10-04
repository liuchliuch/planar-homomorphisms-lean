import PlanarHom.OccurrenceKasteleynFanOrientation

/-! NEW literal tree-band contour sides. Their endpoints are exactly the
minimum/maximum fan endpoints identified by the geometric orientation theorem.
Both directions are separate closed arcs, with proved global separation. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

/-- Starting at the minimum-height endpoint of dart a, cross its actual strip
at fixed transverse coordinate to the maximum endpoint of the reverse dart. -/
def boundarySide (a : Dart E) : C(I,Plane) where
  toFun t := C.band Function.injective_id a.1
    (outgoingParameter a.2 t,enterParameter positive a)
  continuous_toFun := (C.band Function.injective_id a.1).continuous.comp (by
    cases a.2 <;> simp only [outgoingParameter,Bool.false_eq_true,if_false,if_true] <;> fun_prop)

@[simp] theorem boundarySide_zero (a : Dart E) :
    C.boundarySide a 0=C.port a (enterParameter positive a) := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [boundarySide,port,outgoingParameter]

@[simp] theorem boundarySide_one (a : Dart E) :
    C.boundarySide a 1=C.port (a.1,!a.2) (exitParameter positive (a.1,!a.2)) := by
  rw [← enter_eq_exit_reverse positive a]
  rcases a with ⟨e,b⟩
  cases b <;> simp [boundarySide,port,outgoingParameter]

theorem boundarySide_injective (a : Dart E) : Function.Injective (C.boundarySide a) := by
  intro s t h
  have hp := (C.band_isClosedEmbedding Function.injective_id a.1).injective h
  have ht := congrArg Prod.fst hp
  cases hb : a.2 <;> simpa only [outgoingParameter,hb,Bool.false_eq_true,if_false,if_true,
    unitInterval.symm_inj] using ht

/-- All oriented side arcs are pairwise disjoint, including opposite sides of
one tree occurrence. Thus selected-tree reversal joins exactly the intended ports. -/
theorem boundarySides_disjoint {a b : Dart E} (hab : a≠b) :
    Disjoint (Set.range (C.boundarySide a)) (Set.range (C.boundarySide b)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs⟩ ⟨t,ht⟩
  have h := hs.trans ht.symm
  rcases a with ⟨e,be⟩
  rcases b with ⟨f,bf⟩
  by_cases hef : e=f
  · subst f
    have hp := (C.band_isClosedEmbedding Function.injective_id e).injective h
    have htrans := congrArg Prod.snd hp
    cases positive <;> cases be <;> cases bf
    all_goals first | exact hab rfl | norm_num [enterParameter] at htrans
  · exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hef)
      ⟨(outgoingParameter be s,enterParameter positive (e,be)),rfl⟩
      ⟨(outgoingParameter bf t,enterParameter positive (f,bf)),h.symm⟩

/-- An interior side point lies strictly beyond every host circle. -/
theorem boundarySide_outside (a : Dart E) (t : I) (ht : Inside t) (v : V) :
    C.radius<rayLength (C.boundarySide a t-d.drawing.point v) := by
  apply C.band_outside Function.injective_id a.1
    (outgoingParameter a.2 t,enterParameter positive a) _ v
  cases hb : a.2
  · change Inside (unitInterval.symm t)
    constructor <;> change _ < _ <;> simp only [unitInterval.coe_symm_eq] <;> linarith [ht.1,ht.2]
  · exact ht

/-- A selected side never meets a different occurrence's complete closed band,
so in particular it avoids every retained non-tree return slice. -/
theorem boundarySide_disjoint_band {a : Dart E} {e : E} (hae : a.1≠e) :
    Disjoint (Set.range (C.boundarySide a)) (Set.range (C.band Function.injective_id e)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs⟩ hx
  exact Set.disjoint_left.mp (C.bands_disjoint Function.injective_id hae)
    ⟨(outgoingParameter a.2 s,enterParameter positive a),hs⟩ hx

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

import PlanarHom.OccurrenceKasteleynBandLanes
import PlanarHom.PlanarityLRCyclicBlockInputs

/-! NEW complete local rootward routing from the literal geometric row.
The input word is computed by dropping the parent, scanning its suffix, then
its prefix, and expanding the supplied child-port blocks. The numeric circular
order required by disk routing is proved from actual fan gaps. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}

omit [Fintype V] [Fintype E] in
theorem hostDart_edge_ne_of_ne {v : V} {a p : HostDart G v}
    (hp : G.src p.val.1≠G.dst p.val.1) (hap : a≠p) : a.val.1≠p.val.1 := by
  intro he
  have hs : (G.dartPair a.val).1=(G.dartPair p.val).1 := a.property.trans p.property.symm
  by_cases hb : a.val.2=p.val.2
  · exact hap (Subtype.ext (Prod.ext he hb))
  · have hb' : a.val.2=(!p.val.2) := Bool.eq_not_iff.mpr hb
    simp only [dartPair,he,hb'] at hs
    cases hdir : p.val.2 <;> simp only [hdir,Bool.not_false,Bool.not_true,if_true,
      Bool.false_eq_true,if_false] at hs
    · exact hp hs
    · exact hp hs.symm

namespace HostFanChart
variable {v : V} (H : HostFanChart F v) {A : Type*}

/-- Named child ports, retaining arbitrary original labels and actual fan
coordinates. The row scan omits only the parent block. -/
def rootwardInputWord (p : HostDart G v) (block : HostDart G v → List (A×I)) :
    List (A × (HostDart G v × I)) := by
  classical
  exact afterParentInputs H.row p (fun a => (block a).map (fun x => (x.1,(a,x.2))))

def rootwardInput (p : HostDart G v) (block : HostDart G v → List (A×I))
    (i : Fin (H.rootwardInputWord p block).length) : HostDart G v × I :=
  ((H.rootwardInputWord p block).get i).2

def rootwardLabel (p : HostDart G v) (block : HostDart G v → List (A×I))
    (i : Fin (H.rootwardInputWord p block).length) : A :=
  ((H.rootwardInputWord p block).get i).1

private theorem liftedBlock_bounds (block : HostDart G v → List (A×I))
    (a : HostDart G v) (x : A × (HostDart G v × I))
    (hx : x∈(block a).map (fun y => (y.1,(a,y.2)))) :
    H.lower a≤H.height x.2.1 x.2.2 ∧ H.height x.2.1 x.2.2≤H.upper a := by
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  rw [← Set.mem_Icc,← H.height_range]
  exact ⟨y.2,rfl⟩

private theorem liftedBlock_sorted (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (a : HostDart G v) :
    ((block a).map (fun y => (y.1,(a,y.2)))).Pairwise
      (fun x y => H.height x.2.1 x.2.2<H.height y.2.1 y.2.2) := by
  simpa only [List.pairwise_map] using hblock a

theorem rootwardInput_order (p : HostDart G v) (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (i j : Fin (H.rootwardInputWord p block).length) (hij : i<j) :
    AfterGapOrder (H.lower p) (H.upper p)
      (H.height (H.rootwardInput p block i).1 (H.rootwardInput p block i).2)
      (H.height (H.rootwardInput p block j).1 (H.rootwardInput p block j).2) := by
  classical
  exact afterParentInputs_indexed_order H.row p _ H.lower H.upper
    (fun x : A × (HostDart G v × I) => H.height x.2.1 x.2.2) (H.mem_row p) H.row_strict_gaps
    (H.liftedBlock_sorted block hblock) (H.liftedBlock_bounds block) i j hij

theorem rootwardInput_outside (p : HostDart G v) (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (i : Fin (H.rootwardInputWord p block).length) :
    H.height (H.rootwardInput p block i).1 (H.rootwardInput p block i).2<H.lower p ∨
      H.upper p<H.height (H.rootwardInput p block i).1 (H.rootwardInput p block i).2 := by
  classical
  exact (afterParentInputs_spec H.row p _ H.lower H.upper (fun x : A × (HostDart G v × I) => H.height x.2.1 x.2.2)
    (H.mem_row p) H.row_strict_gaps (H.liftedBlock_sorted block hblock)
    (H.liftedBlock_bounds block)).2 _ (List.get_mem _ _)

theorem rootwardInput_ne_parent (p : HostDart G v) (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (i : Fin (H.rootwardInputWord p block).length) : (H.rootwardInput p block i).1≠p := by
  intro he
  have ho := H.rootwardInput_outside p block hblock i
  rw [he] at ho
  have hb : H.height p (H.rootwardInput p block i).2∈Icc (H.lower p) (H.upper p) := by
    rw [← H.height_range]
    exact ⟨_,rfl⟩
  exact ho.elim (not_lt_of_ge hb.1) (not_lt_of_ge hb.2)

/-- Literal named output block to be supplied to the next parent. -/
def rootwardOutputBlock (p : HostDart G v) (block : HostDart G v → List (A×I)) : List (A×I) :=
  List.ofFn (fun i : Fin (H.rootwardInputWord p block).length =>
    (H.rootwardLabel p block i,H.slotParameter p (H.rootwardInputWord p block).length i))

@[simp] theorem rootwardOutputBlock_length (p : HostDart G v) (block : HostDart G v → List (A×I)) :
    (H.rootwardOutputBlock p block).length=(H.rootwardInputWord p block).length := by
  simp [rootwardOutputBlock]

theorem rootwardOutputBlock_sorted {w : V} (K : HostFanChart F w)
    (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (A×I)) :
    (H.rootwardOutputBlock p block).Pairwise (fun x y => K.height q x.2<K.height q y.2) := by
  rw [rootwardOutputBlock,List.pairwise_ofFn]
  intro i j hij
  exact H.opposite_slot_heights_strictMono K p q hq _ hij

theorem rootwardOutputBlock_labels (p : HostDart G v) (block : HostDart G v → List (A×I)) :
    (H.rootwardOutputBlock p block).map Prod.fst=(H.rootwardInputWord p block).map Prod.fst := by
  simp only [rootwardOutputBlock,List.map_ofFn,Function.comp_def,rootwardLabel]
  simpa only [List.map_ofFn,Function.comp_def] using
    congrArg (List.map Prod.fst) (List.ofFn_get (H.rootwardInputWord p block))

end HostFanChart

namespace CircleClipping
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v) {A : Type*}

/-- The literal row-expanded finite family of actual disk-then-band paths. -/
def localRootwardFamily (p : HostDart G v) (block : HostDart G v → List (A×I))
    (i : Fin (H.rootwardInputWord p block).length) :=
  C.rootwardStep H p (H.rootwardInputWord p block).length (H.rootwardInput p block) i

theorem localRootwardFamily_injective (p : HostDart G v) (hp : G.src p.val.1≠G.dst p.val.1)
    (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (i : Fin (H.rootwardInputWord p block).length) :
    Function.Injective (C.localRootwardFamily H p block i) :=
  C.rootwardStep_injective H p _ _
    (fun i => hostDart_edge_ne_of_ne hp (H.rootwardInput_ne_parent p block hblock i)) i

theorem localRootwardFamily_disjoint (p : HostDart G v) (hp : G.src p.val.1≠G.dst p.val.1)
    (block : HostDart G v → List (A×I))
    (hblock : ∀ a, (block a).Pairwise (fun x y => H.height a x.2<H.height a y.2))
    (i j : Fin (H.rootwardInputWord p block).length) (hne : i≠j) :
    Disjoint (Set.range (C.localRootwardFamily H p block i))
      (Set.range (C.localRootwardFamily H p block j)) :=
  C.rootwardSteps_disjoint H p _ _
    (fun i => hostDart_edge_ne_of_ne hp (H.rootwardInput_ne_parent p block hblock i))
    (H.rootwardInput_order p block hblock) i j hne

/-- Output order at the opposite host is increasing in the exact emitted word,
so this family is a valid child block for the next rooted induction step. -/
theorem localRootwardFamily_output_order {w : V} (K : HostFanChart F w)
    (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (A×I)) :
    StrictMono (fun i : Fin (H.rootwardInputWord p block).length =>
      K.height q (H.slotParameter p (H.rootwardInputWord p block).length i)) :=
  H.opposite_slot_heights_strictMono K p q hq _

end CircleClipping
end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

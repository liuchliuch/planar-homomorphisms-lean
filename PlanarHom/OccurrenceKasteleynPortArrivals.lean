import PlanarHom.RootedOccurrenceTreeCuts

/-! NEW concrete named arriving ports for finite subtree recursion. Every
arrival records an actual local port or child path with its original dart
source. Local row expansion retains that source and the actual endpoint. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.IncomingLane
variable {x y : Plane}

def cast (h : x=y) (p : IncomingLane x) : IncomingLane y := h ▸ p

@[simp] theorem cast_source (h : x=y) (p : IncomingLane x) : (p.cast h).source=p.source := by
  subst y
  rfl

@[simp] theorem cast_trace (h : x=y) (p : IncomingLane x) : (p.cast h).trace=p.trace := by
  subst y
  rfl

@[simp] theorem cast_simple (h : x=y) (p : IncomingLane x) : (p.cast h).Simple ↔ p.Simple := by
  subst y
  rfl

end PlanarHom.MultiGraph.IncomingLane

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

/-- An original retained dart transported to one named actual host fan. -/
structure PortArrival (v : V) where
  label : Dart E
  dart : HostDart G v
  parameter : I
  incoming : IncomingLane (C.port dart.val parameter)
  source_eq : incoming.source=C.port label 0

namespace PortArrival
variable {C} {v : V}

def localPort (a : HostDart G v) : C.PortArrival v where
  label := a.val
  dart := a
  parameter := 0
  incoming := .localPort
  source_eq := rfl

def trace (x : C.PortArrival v) : Set Plane := x.incoming.trace
def Simple (x : C.PortArrival v) : Prop := x.incoming.Simple

@[simp] theorem localPort_trace (a : HostDart G v) : (localPort (C:=C) a).trace={C.port a.val 0} := rfl

@[simp] theorem localPort_simple (a : HostDart G v) : (localPort (C:=C) a).Simple := trivial

def castHost {w : V} (h : v=w) (x : C.PortArrival v) : C.PortArrival w := h ▸ x

@[simp] theorem castHost_label {w : V} (h : v=w) (x : C.PortArrival v) : (x.castHost h).label=x.label := by
  subst w
  rfl

@[simp] theorem castHost_parameter {w : V} (h : v=w) (x : C.PortArrival v) :
    (x.castHost h).parameter=x.parameter := by
  subst w
  rfl

@[simp] theorem castHost_dart {w : V} (h : v=w) (x : C.PortArrival v) :
    (x.castHost h).dart.val=x.dart.val := by
  subst w
  rfl

@[simp] theorem castHost_trace {w : V} (h : v=w) (x : C.PortArrival v) : (x.castHost h).trace=x.trace := by
  subst w
  rfl

@[simp] theorem castHost_simple {w : V} (h : v=w) (x : C.PortArrival v) :
    (x.castHost h).Simple ↔ x.Simple := by
  subst w
  rfl

theorem source_mem_trace (x : C.PortArrival v) : C.port x.label 0∈x.trace := by
  rw [← x.source_eq]
  exact x.incoming.source_mem_trace

theorem target_mem_trace (x : C.PortArrival v) : C.port x.dart.val x.parameter∈x.trace :=
  x.incoming.target_mem_trace

end PortArrival

variable {v : V} (H : HostFanChart F v)

def arrivalBlock (block : HostDart G v → List (C.PortArrival v)) (a : HostDart G v) :
    List (C.PortArrival v × I) := (block a).map (fun x => (x,x.parameter))

abbrev arrivalCount (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v)) : ℕ :=
  (H.rootwardInputWord p (C.arrivalBlock block)).length

def scannedArrival (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (i : Fin (C.arrivalCount H p block)) : C.PortArrival v :=
  H.rootwardLabel p (C.arrivalBlock block) i

theorem scannedArrival_mem (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (i : Fin (C.arrivalCount H p block)) : ∃ a, C.scannedArrival H p block i∈block a := by
  classical
  have hm := List.get_mem (H.rootwardInputWord p (C.arrivalBlock block)) i
  unfold HostFanChart.rootwardInputWord afterParentInputs at hm
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,arrivalBlock] at hm
  rcases hm with ⟨a,_,y,hy,he⟩ | ⟨a,_,y,hy,he⟩
  all_goals obtain ⟨x,hx,hxy⟩ := hy
  all_goals subst y
  all_goals refine ⟨a,?_⟩
  all_goals have he' := he.symm
  all_goals change (H.rootwardInputWord p (C.arrivalBlock block)).get i=(x,(a,x.parameter)) at he'
  all_goals unfold scannedArrival HostFanChart.rootwardLabel
  all_goals rw [he']
  all_goals exact hx

theorem scannedArrival_input (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (hplace : ∀ a x, x∈block a → x.dart=a) (i : Fin (C.arrivalCount H p block)) :
    H.rootwardInput p (C.arrivalBlock block) i=
      ((C.scannedArrival H p block i).dart,(C.scannedArrival H p block i).parameter) := by
  classical
  have hm := List.get_mem (H.rootwardInputWord p (C.arrivalBlock block)) i
  unfold HostFanChart.rootwardInputWord afterParentInputs at hm
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,arrivalBlock] at hm
  rcases hm with ⟨a,_,y,hy,he⟩ | ⟨a,_,y,hy,he⟩
  all_goals obtain ⟨x,hx,hxy⟩ := hy
  all_goals subst y
  all_goals have he' := he.symm
  all_goals change (H.rootwardInputWord p (C.arrivalBlock block)).get i=(x,(a,x.parameter)) at he'
  all_goals unfold HostFanChart.rootwardInput scannedArrival HostFanChart.rootwardLabel
  all_goals rw [he',hplace a x hx]

theorem arrivalBlock_sorted (block : HostDart G v → List (C.PortArrival v))
    (hsort : ∀ a, (block a).Pairwise (fun x y => H.height a x.parameter<H.height a y.parameter)) :
    ∀ a, (C.arrivalBlock block a).Pairwise (fun x y => H.height a x.2<H.height a y.2) := by
  intro a
  simpa only [arrivalBlock,List.pairwise_map] using hsort a

theorem scannedArrival_injective (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (hplace : ∀ a x, x∈block a → x.dart=a)
    (hsort : ∀ a, (block a).Pairwise (fun x y => H.height a x.parameter<H.height a y.parameter)) :
    Function.Injective (C.scannedArrival H p block) := by
  have hlt (i j : Fin (C.arrivalCount H p block)) (hij : i<j) :
      C.scannedArrival H p block i≠C.scannedArrival H p block j := by
    intro he
    have hh := H.rootwardInput_order p (C.arrivalBlock block) (C.arrivalBlock_sorted H block hsort) i j hij
    rw [C.scannedArrival_input H p block hplace i,C.scannedArrival_input H p block hplace j,he] at hh
    have hp := H.lower_lt_upper p
    rcases hh with hh | hh | hh <;> dsimp at hh <;> linarith [hh.1,hh.2]
  intro i j he
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact hlt i j hij he
  · exact hlt j i hji he.symm

def scannedIncoming (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (hplace : ∀ a x, x∈block a → x.dart=a) (i : Fin (C.arrivalCount H p block)) :
    IncomingLane (C.port (H.rootwardInput p (C.arrivalBlock block) i).1.val
      (H.rootwardInput p (C.arrivalBlock block) i).2) :=
  (C.scannedArrival H p block i).incoming.cast
    (congrArg (fun q : HostDart G v × I => C.port q.1.val q.2) (C.scannedArrival_input H p block hplace i).symm)

@[simp] theorem scannedIncoming_trace (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (hplace : ∀ a x, x∈block a → x.dart=a) (i : Fin (C.arrivalCount H p block)) :
    (C.scannedIncoming H p block hplace i).trace=(C.scannedArrival H p block i).trace := by
  exact IncomingLane.cast_trace _ _

@[simp] theorem scannedIncoming_source (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v))
    (hplace : ∀ a x, x∈block a → x.dart=a) (i : Fin (C.arrivalCount H p block)) :
    (C.scannedIncoming H p block hplace i).source=C.port (C.scannedArrival H p block i).label 0 := by
  rw [scannedIncoming,IncomingLane.cast_source]
  exact (C.scannedArrival H p block i).source_eq

/-- One named output arrival, carrying the whole old path joined to the new
literal local step. The original dart source is preserved exactly. -/
def routedArrival {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (hplace : ∀ a x, x∈block a → x.dart=a)
    (i : Fin (C.arrivalCount H p block)) : C.PortArrival w where
  label := (C.scannedArrival H p block i).label
  dart := q
  parameter := H.slotParameter p (C.arrivalCount H p block) i
  incoming := .child (C.port (C.scannedArrival H p block i).label 0)
    ((C.joinedRootward H p _ _ (C.scannedIncoming H p block hplace) i).cast
      (C.scannedIncoming_source H p block hplace i).symm (congrArg (fun a => C.port a _) hq))
  source_eq := rfl

theorem routedArrival_trace {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (hplace : ∀ a x, x∈block a → x.dart=a)
    (i : Fin (C.arrivalCount H p block)) :
    (C.routedArrival H p q hq block hplace i).trace=
      (C.scannedArrival H p block i).trace ∪
        Set.range (C.rootwardStep H p _ (H.rootwardInput p (C.arrivalBlock block)) i) := by
  change Set.range (C.joinedRootward H p _ _ (C.scannedIncoming H p block hplace) i)=_
  rw [C.joinedRootward_range,C.scannedIncoming_trace]

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

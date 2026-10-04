import PlanarHom.PlanarityRowComponentFaceProducts
import PlanarHom.PlanarityLRComponentCycleFlip
import PlanarHom.PlanarityLRComponentConnected
import PlanarHom.OccurrenceFiniteKasteleynCycle
import PlanarHom.OccurrenceKasteleynCycleFlipSigns
import PlanarHom.PlanarityRowFaceMachines

/-! NEW Pfaffian correctness of the actual arbitrary-row orientation compiler.
Its input consists only of raw numeric rows; realization and component Euler
are exact proved semantic properties of those rows. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization FinitePermutationCycles

 def ComponentEuler (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) : Prop :=
  ∀r : Fin g.vertices,PlanarityDepthFirstSearch.height g r.val=0 → Nonempty (ComponentEdge g r.val) →
    Nat.card (ComponentVertex g r.val)+count (componentFace g hg r.val R)=Nat.card (ComponentEdge g r.val)+2

 theorem orientationLog_cycle_odd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (hEuler : ComponentEuler g hg R) {M N : Finset (Fin g.edges.length)}
    (flip : AlternatingCycleFlip (g.toMultiGraph hg) M N) :
    boundarySign (fun e : Fin g.edges.length=>logOrientation (orientationLog g rows) e.val)
      flip.cycle.cycleDarts= -1 := by
  classical
  let r := PlanarityLRRealization.DirectedSimpleCycle.componentIndex g hg flip.cycle
  have hr : PlanarityDepthFirstSearch.height g r.val=0 :=
    PlanarityLRRealization.DirectedSimpleCycle.componentIndex_height g hg flip.cycle
  let lifted := componentFlip g hg flip
  let base := lifted.cycle.dart ⟨0,by have := lifted.cycle.length_ge_two; omega⟩
  let cr := componentRows g hg r.val R
  let omitted := componentFaceRoot g hg rows R hrows r.val base
  have heuler : Fintype.card (ComponentVertex g r.val)+Fintype.card cr.Face=
      Fintype.card (ComponentEdge g r.val)+2 := by
    have hh := hEuler r hr ⟨base.1⟩
    simpa only [count,Nat.card_eq_fintype_card,RotationRows.Face,cr,componentFace,RotationRows.facePerm] using hh
  have hfaces : ∀q : cr.Face,q≠cr.faceOf omitted →
      (∏a : {a : Dart (ComponentEdge g r.val) // cr.faceOf a=q},
        dartSign (componentOrientation g r.val (logOrientation (orientationLog g rows))) a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart (ComponentEdge g r.val) // cr.faceOf a=q}+1) := by
    intro q hq
    convert orientationLog_component_face_products g hg rows R hrows r.val base q hq using 1 <;>
      congr <;> exact Subsingleton.elim _ _
  have h := cr.alternatingCycle_boundarySign_neg_one_of_euler omitted
    (componentGraph_connected g hg r hr) heuler
    (componentOrientation g r.val (logOrientation (orientationLog g rows))) hfaces lifted
  rw [componentFlip_boundarySign] at h
  exact h

 theorem orientationLog_isPfaffian (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (hEuler : ComponentEuler g hg R) :
    (g.toMultiGraph hg).IsPfaffianOrientation (fun e=>logOrientation (orientationLog g rows) e.val) := by
  apply isPfaffianOrientation_of_odd_cycleFlips
  intro M N flip
  exact orientationLog_cycle_odd g hg rows R hrows hEuler flip

 theorem certified_orientationLog :
    FP inputCode logCode (fun p=>orientationLog p.1 p.2) ∧
    ∀(g : MixedCode) (bt ut : ℕ) (hg : g.Valid bt ut) (rows : Rows)
      (R : RotationRows (g.toMultiGraph hg)), Realizes g hg rows R → ComponentEuler g hg R →
        (g.toMultiGraph hg).IsPfaffianOrientation (fun e=>logOrientation (orientationLog g rows) e.val) :=
  ⟨fp_orientationLog,fun g _ _ hg rows R hrows hEuler=>orientationLog_isPfaffian g hg rows R hrows hEuler⟩

end PlanarHom.PlanarityRowFaceCode

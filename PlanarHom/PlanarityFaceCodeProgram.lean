import PlanarHom.PlanarityLRDirectMachines

/-! NEW reconstruction. Literal bounded raw dart-orbit and full face-table
materialization. No root/exterior-face oracle is used or asserted here. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRConstraints

 def walk (g : MixedCode) (bits : List Bool) (a : Dart) (n : ℕ) : List Dart :=
   (List.range n).map (fun i=>(faceStep g bits)^[i] a)
 def orbit (g : MixedCode) (bits : List Bool) (a : Dart) : List Dart := walk g bits a (2*g.edges.length)
 def boundary (g : MixedCode) (bits : List Bool) (a : Dart) : List Dart :=
   (orbit g bits a).take 1 ++ (orbit g bits a).tail.takeWhile (fun b=>b != a)
 def representative (g : MixedCode) (bits : List Bool) (a : Dart) : Dart :=
   ((allDarts g).filter (fun b=>decide (b∈orbit g bits a))).headD a
 def representatives (g : MixedCode) (bits : List Bool) : List Dart :=
   (allDarts g).filter (fun a=>decide (representative g bits a=a))
 def fullTable (g : MixedCode) (bits : List Bool) : List MultiGraph.Kasteleyn.RawFace :=
   (representatives g bits).zipIdx.map (fun p=>(p.2,boundary g bits p.1))
 def computedTable (g : MixedCode) : List MultiGraph.Kasteleyn.RawFace := fullTable g (decideAligned g).2

@[simp] theorem walk_length (g : MixedCode) (bits : List Bool) (a : Dart) (n : ℕ) :
    (walk g bits a n).length=n := by simp [walk]
@[simp] theorem orbit_length (g : MixedCode) (bits : List Bool) (a : Dart) :
    (orbit g bits a).length=2*g.edges.length := walk_length _ _ _ _
 theorem boundary_length (g : MixedCode) (bits : List Bool) (a : Dart) :
    (boundary g bits a).length≤2*g.edges.length := by
  have hh:=(List.takeWhile_sublist (p := fun b=>b != a) (l := (orbit g bits a).tail)).length_le
  simp only [boundary,List.length_append,List.length_take,List.length_tail,orbit_length] at hh ⊢
  omega
 theorem representatives_nodup (g : MixedCode) (bits : List Bool) : (representatives g bits).Nodup :=
   (allDarts_nodup g).filter _
 theorem fullTable_length (g : MixedCode) (bits : List Bool) : (fullTable g bits).length≤2*g.edges.length := by
  have hh:=List.length_filter_le (fun a=>decide (representative g bits a=a)) (allDarts g)
  simpa [fullTable,representatives] using hh

end PlanarHom.PlanarityFaceCode

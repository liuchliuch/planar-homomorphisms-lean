import PlanarHom.PlanarityFaceRootMachines
import PlanarHom.PlanarityLRRealizationRotationSystem
import PlanarHom.FisherExpansionMachines

/-! NEW literal face/orientation compiler for explicitly materialized numeric
rotation rows. The program accepts ordinary lists; semantic realization and
component Euler are separate proved properties of its actual input rows. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect
abbrev Rows := List (List Dart)
abbrev rowsCode := dartCode.list.list
abbrev inputCode := MixedCode.encoding.prod rowsCode

 def rotation (g : MixedCode) (rows : Rows) (a : Dart) : Dart :=
  rowNext (rows.getD (host g a) []) a
 def faceStep (g : MixedCode) (rows : Rows) (a : Dart) : Dart := rotation g rows (reverse a)
 def walk (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) : List Dart :=
  (List.range n).map (fun i=>(faceStep g rows)^[i] a)
 def orbit (g : MixedCode) (rows : Rows) (a : Dart) : List Dart := walk g rows a (2*g.edges.length)
 def boundary (g : MixedCode) (rows : Rows) (a : Dart) : List Dart :=
  (orbit g rows a).take 1 ++ (orbit g rows a).tail.takeWhile (fun b=>b != a)
 def representative (g : MixedCode) (rows : Rows) (a : Dart) : Dart :=
  ((allDarts g).filter (fun b=>decide (b∈orbit g rows a))).headD a
 def representatives (g : MixedCode) (rows : Rows) : List Dart :=
  (allDarts g).filter (fun a=>decide (representative g rows a=a))
 def fullTable (g : MixedCode) (rows : Rows) : List MultiGraph.Kasteleyn.RawFace :=
  (representatives g rows).zipIdx.map (fun p=>(p.2,boundary g rows p.1))
 def rootRepresentative (g : MixedCode) (rows : Rows) (a : Dart) : Dart :=
  ((representatives g rows).filter (fun b=>decide
    (componentRoot g (host g b)=componentRoot g (host g a)))).headD a
 def boundedTable (g : MixedCode) (rows : Rows) : List MultiGraph.Kasteleyn.RawFace :=
  ((representatives g rows).zipIdx.filter (fun p=>decide (rootRepresentative g rows p.1≠p.1))).map
    (fun p=>(p.2,boundary g rows p.1))
 def orientationLog (g : MixedCode) (rows : Rows) : List ℕ :=
  MultiGraph.Kasteleyn.computeOrientation (boundedTable g rows)

 def Realizes (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows)
    (R : PlanarityLRRealization.RotationRows (g.toMultiGraph hg)) : Prop :=
  ∀v:Fin g.vertices,rows.getD v.val []=(R.row v).map PlanarityLRRealization.eraseDart

@[simp] theorem walk_length (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) : (walk g rows a n).length=n := by simp [walk]
@[simp] theorem orbit_length (g : MixedCode) (rows : Rows) (a : Dart) : (orbit g rows a).length=2*g.edges.length := walk_length _ _ _ _
 theorem representatives_nodup (g : MixedCode) (rows : Rows) : (representatives g rows).Nodup := (allDarts_nodup g).filter _
 theorem boundedTable_sublist (g : MixedCode) (rows : Rows) : (boundedTable g rows).Sublist (fullTable g rows) :=
  (List.filter_sublist (l:=(representatives g rows).zipIdx)).map _

end PlanarHom.PlanarityRowFaceCode

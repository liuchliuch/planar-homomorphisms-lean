import PlanarHom.SurfaceRawEmbeddingCode
import PlanarHom.PlanarityRowFaceMachines
import PlanarHom.PlanarityRowComponentFaceRoot
import PlanarHom.PlanarityLRDirectMachines

/-! NEW actual planar-input compiler into finite supplied-surface data.
All non-root face regions are indexed densely; the single outer region contains
the omitted face of every nonempty component and every isolated boundary. -/
namespace PlanarHom.SurfacePlanarCompiler
open Complexity PlanarityLRDirect PlanarityLRConstraints PlanarityLRRealization
open PlanarityRotationCode SurfaceRawEmbedding

 def rows (g : MixedCode) : PlanarityRowFaceCode.Rows :=
  (List.range g.vertices).map (directRow g (decideAligned g).2)

 def disks (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : List Dart :=
  (PlanarityRowFaceCode.representatives g rows).filter
    (fun a=>decide (PlanarityRowFaceCode.rootRepresentative g rows a≠a))

 def region (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) (a : Dart) : ℕ :=
  let r:=PlanarityRowFaceCode.representative g rows a
  if PlanarityRowFaceCode.rootRepresentative g rows r=r then 0 else (disks g rows).idxOf r+1

 def complement (ambient : ℕ) (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : ComplementCode where
  genera:=ambient::(disks g rows).map (fun _=>0)
  dartRegion:=(List.range g.edges.length).flatMap (fun e=>[region g rows (e,false),region g rows (e,true)])
  isolatedRegion:=(List.range g.vertices).map (fun _=>0)

 def compile (ambient : ℕ) (g : MixedCode) : Input := (g,rows g,complement ambient g (rows g))

 theorem rows_realizes (g : MixedCode) {bt ut : ℕ} (hg:g.Valid bt ut) :
    PlanarityRowFaceCode.Realizes g hg (rows g) (directRotationRows g hg (decideAligned g).2) := by
  intro v
  change ((List.range g.vertices).map (directRow g (decideAligned g).2)).getD v.val []=
    (typedDirectRow g hg (decideAligned g).2 v).map eraseDart
  rw [erase_typedDirectRow]
  simp [List.getD_eq_getElem?_getD,v.isLt]

@[simp] theorem compile_graph (ambient : ℕ) (g : MixedCode) : (compile ambient g).1=g := rfl
@[simp] theorem complement_regions (ambient : ℕ) (g : MixedCode) (r : PlanarityRowFaceCode.Rows) :
    (complement ambient g r).genera.length=(disks g r).length+1 := by simp [complement,Nat.add_comm]
@[simp] theorem complement_dart_length (ambient : ℕ) (g : MixedCode) (r : PlanarityRowFaceCode.Rows) :
    (complement ambient g r).dartRegion.length=2*g.edges.length := by
  simp [complement,List.length_flatMap,Nat.mul_comm]
@[simp] theorem complement_isolated_length (ambient : ℕ) (g : MixedCode) (r : PlanarityRowFaceCode.Rows) :
    (complement ambient g r).isolatedRegion.length=g.vertices := by simp [complement]

end PlanarHom.SurfacePlanarCompiler

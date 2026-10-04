import PlanarHom.SurfaceBoundaryRootSelection
import PlanarHom.SurfacePlanarComplementTables

/-! NEW actual incidence connectivity and Euler validity of the compiled
complement. The only extra hypothesis here is the proved genus-zero row Euler
equation, discharged for ordinary planar input in the final source adapter. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfacePlanarCompiler
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open SurfaceRibbonComplement SurfaceRawEmbedding PlanarityRowFaceCode
variable (ambient:ℕ) (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (rs:Rows)
variable (R:RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R)

 def compiledData : Data R := ComplementCode.toData (complement_wellFormed ambient g hg rs R hrs)

 theorem compiledData_regions : (compiledData ambient g hg rs R hrs).regions=(disks g rs).length+1 :=
  complement_regions ambient g rs
 theorem compiledData_genus : (∑j,(compiledData ambient g hg rs R hrs).regionGenus j)=ambient :=
  complement_genus_sum ambient g rs

 theorem compiledData_face (a:FaceRep g rs) :
    ((compiledData ambient g hg rs R hrs).attachment (.inl (representativeFace g hg rs R a))).val=
      if rootRepresentative g rs a.val=a.val then 0 else (disks g rs).idxOf a.val+1 := by
  change ((ComplementCode.toData (complement_wellFormed ambient g hg rs R hrs)).attachment
    (.inl (R.faceOf (liftDart a.val _)))).val=_
  rw [ComplementCode.toData_face,complement_dartLabel,erase_liftDart]
  simp only [region,representative_fixed_of_mem g rs a.property]

 theorem compiledData_root (b:Boundary R) (hb:IsRootBoundary g hg rs R hrs b) :
    ((compiledData ambient g hg rs R hrs).attachment b).val=0 := by
  cases b with
  | inr v=>
    change (complement ambient g rs).isolatedLabel v.val.val=0
    exact complement_isolatedLabel _ _ _ _
  | inl f=>
    rw [←representativeFace_left g hg rs R hrs f,compiledData_face]
    exact if_pos hb

 theorem compiledData_disk (k:Fin (typedDisks g hg rs R).length) :
    ((compiledData ambient g hg rs R hrs).attachment ((typedDisks g hg rs R).get k)).val=k.val+1 := by
  have hk:k.val<(disks g rs).length := by simpa only [typedDisks_length] using k.isLt
  let a:FaceRep g rs:=⟨(disks g rs)[k.val],(List.mem_filter.mp (List.getElem_mem hk)).1⟩
  have he:(typedDisks g hg rs R).get k=.inl (representativeFace g hg rs R a) := by
    simp [typedDisks,List.get_eq_getElem,a]
  rw [he,compiledData_face]
  have hn:rootRepresentative g rs a.val≠a.val :=
    of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hk)).2
  rw [if_neg hn]
  congr 1
  change (disks g rs).idxOf ((disks g rs)[k.val])=k.val
  rw [dart_idxOf_decidable]
  exact List.idxOf_getElem ((representatives_nodup g rs).filter _) k.val hk

 theorem complement_valid_of_euler
    (he:g.vertices+Fintype.card (Boundary R)=g.edges.length+2*(g.toMultiGraph hg).componentCount Finset.univ) :
    (compiledData ambient g hg rs R hrs).Valid ambient := by
  let D:=compiledData ambient g hg rs R hrs
  let P:=rootedPartition g hg rs R hrs
  have hlen:P.disks.length=(disks g rs).length:=typedDisks_length g hg rs R
  have hq:D.regions=P.disks.length+1 := (compiledData_regions ambient g hg rs R hrs).trans (congrArg (·+1) hlen.symm)
  refine ⟨by rw [hq]; omega,?_,?_⟩
  · exact SurfaceRootedBoundaryPartition.incidence_connected P D.regions hq D.attachment
      (fun c=>compiledData_root ambient g hg rs R hrs _ (chosenRoot_spec g hg rs R hrs c).2)
      (fun k=>compiledData_disk ambient g hg rs R hrs k)
  · have hc:=SurfaceRootedBoundaryPartition.cardinal P
    have hgeneration:=compiledData_genus ambient g hg rs R hrs
    have hv:Fintype.card (Fin g.vertices)=g.vertices:=Fintype.card_fin _
    have hed:Fintype.card (Fin g.edges.length)=g.edges.length:=Fintype.card_fin _
    have hcomp:Fintype.card (Component (G:=g.toMultiGraph hg))=(g.toMultiGraph hg).componentCount Finset.univ:=rfl
    change 2*ambient+Fintype.card (Fin g.vertices)+2*D.regions=
      Fintype.card (Fin g.edges.length)+Fintype.card (Boundary R)+2+2*(∑j,D.regionGenus j)
    change (∑j,D.regionGenus j)=ambient at hgeneration
    omega

end PlanarHom.SurfacePlanarCompiler

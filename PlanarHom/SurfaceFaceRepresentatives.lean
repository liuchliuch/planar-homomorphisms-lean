import PlanarHom.SurfacePlanarComplementProgram

/-! NEW exact face-quotient/representative equivalence for supplied numeric rows. -/
noncomputable section
open Classical
namespace PlanarHom.SurfacePlanarCompiler
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open SurfaceRibbonComplement PlanarityRowFaceCode
variable (g : MixedCode) {bt ut : ℕ} (hg:g.Valid bt ut) (rs : Rows)
variable (R : RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R)

abbrev FaceRep := {a:PlanarityRotationCode.Dart // a∈representatives g rs}

 def faceRepresentative : R.Face→FaceRep g rs :=
  Quotient.lift (fun a=>⟨representative g rs (eraseDart a),representative_mem_representatives g hg rs R hrs a⟩)
    (fun a b hab=>Subtype.ext (representative_eq_of_sameCycle g hg rs R hrs a b hab))

 def representativeFace (a:FaceRep g rs) : R.Face :=
  R.faceOf (liftDart a.val (representative_index_of_mem g rs a.property))

@[simp] theorem faceRepresentative_of (a:Dart (Fin g.edges.length)) :
    (faceRepresentative g hg rs R hrs (R.faceOf a)).val=representative g rs (eraseDart a) := rfl

 theorem representativeFace_left (f:R.Face) :
    representativeFace g hg rs R (faceRepresentative g hg rs R hrs f)=f := by
  induction f using Quotient.inductionOn with | h a=>
    apply Quotient.sound
    apply (sameCycle_of_representative_eq g hg rs R hrs _ a)
    simp only [representativeFace,faceRepresentative,RotationRows.faceOf,Quotient.lift_mk,erase_liftDart]
    exact representative_idempotent g hg rs R hrs a

 theorem representativeFace_right (a:FaceRep g rs) :
    faceRepresentative g hg rs R hrs (representativeFace g hg rs R a)=a := by
  apply Subtype.ext
  simp only [representativeFace,faceRepresentative_of,erase_liftDart]
  exact representative_fixed_of_mem g rs a.property

 def faceRepEquiv : R.Face≃FaceRep g rs where
  toFun:=faceRepresentative g hg rs R hrs
  invFun:=representativeFace g hg rs R
  left_inv:=representativeFace_left g hg rs R hrs
  right_inv:=representativeFace_right g hg rs R hrs

 def typedDisks : List (Boundary R) :=
  (disks g rs).attach.map (fun a=>Sum.inl (representativeFace g hg rs R
    ⟨a.val,(List.mem_filter.mp a.property).1⟩))

 theorem typedDisks_length : (typedDisks g hg rs R).length=(disks g rs).length := by simp [typedDisks]

 include hrs in
 theorem typedDisks_nodup : (typedDisks g hg rs R).Nodup := by
  apply List.Nodup.map
  · intro a b hab
    apply Subtype.ext
    have hh:=Sum.inl.inj hab
    have he:=congrArg (faceRepresentative g hg rs R hrs) hh
    simp only [representativeFace_right] at he
    exact congrArg (fun z:FaceRep g rs=>z.val) he
  · exact List.nodup_attach.mpr ((representatives_nodup g rs).filter _)

end PlanarHom.SurfacePlanarCompiler

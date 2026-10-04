import PlanarHom.SurfaceFaceRoots
import PlanarHom.PlanarityRowFaceComponents
import PlanarHom.PlanarityRowFaceRoots

/-! NEW actual runtime omitted-face selector on the full disconnected face
quotient. Its idempotence and dual-edge constancy come from the computed DFS
component labels and literal rootRepresentative program. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hr : Realizes g hg rows R)

abbrev Representative (g : MixedCode) (rows : Rows) := {a : PlanarityRotationCode.Dart // a∈representatives g rows}

def faceRepresentative : R.Face→Representative g rows :=
  Quotient.lift (fun a=>⟨representative g rows (eraseDart a),representative_mem_representatives g hg rows R hr a⟩)
    (fun a b h=>Subtype.ext (representative_eq_of_sameCycle g hg rows R hr a b h))

def representativeFace (a : Representative g rows) : R.Face :=
  R.faceOf (liftDart a.val (representative_index_of_mem g rows a.property))

theorem representativeFace_faceRepresentative (q : R.Face) :
    representativeFace g hg rows R (faceRepresentative g hg rows R hr q)=q := by
  induction q using Quotient.inductionOn with
  | h a =>
    let b:=liftDart (representative g rows (eraseDart a))
      (representative_valid g hg rows R hr a)
    have hs:R.facePerm.SameCycle a b:=
      (mem_orbit_iff_sameCycle g hg rows R hr a b).mp (by
        simpa only [b,erase_liftDart] using representative_mem_orbit g hg rows R hr a)
    exact Quotient.sound hs.symm

theorem faceRepresentative_representativeFace (a : Representative g rows) :
    faceRepresentative g hg rows R hr (representativeFace g hg rows R a)=a := by
  apply Subtype.ext
  change representative g rows (eraseDart (liftDart a.val (representative_index_of_mem g rows a.property)))=a.val
  rw [erase_liftDart,representative_fixed_of_mem g rows a.property]

def faceRepresentativeEquiv : R.Face≃Representative g rows where
  toFun:=faceRepresentative g hg rows R hr
  invFun:=representativeFace g hg rows R
  left_inv:=representativeFace_faceRepresentative g hg rows R hr
  right_inv:=faceRepresentative_representativeFace g hg rows R hr

def representativeRoot (a : Representative g rows) : Representative g rows :=
  ⟨rootRepresentative g rows a.val,rootRepresentative_mem g rows a.property⟩

theorem representativeRoot_idempotent (a : Representative g rows) :
    representativeRoot g rows (representativeRoot g rows a)=representativeRoot g rows a :=
  Subtype.ext (rootRepresentative_idempotent g rows a.property)

def runtimeFaceRoots : R.FaceRoots where
  root q:=(faceRepresentativeEquiv g hg rows R hr).symm
    (representativeRoot g rows (faceRepresentativeEquiv g hg rows R hr q))
  idempotent q:=by
    simp only [Equiv.apply_symm_apply,representativeRoot_idempotent]
  across e:=by
    apply congrArg (faceRepresentativeEquiv g hg rows R hr).symm
    apply Subtype.ext
    change rootRepresentative g rows (representative g rows (eraseDart (e,true)))=
      rootRepresentative g rows (representative g rows (eraseDart (e,false)))
    apply rootRepresentative_eq_of_component g rows (representative_mem_representatives g hg rows R hr (e,true))
    rw [representative_componentRoot g hg rows R hr,representative_componentRoot g hg rows R hr]
    exact (reverse_componentRoot g hg (a:=eraseDart (e,true)) e.isLt).symm

theorem runtimeFaceRoots_fixed_iff (q : R.Face) :
    (runtimeFaceRoots g hg rows R hr).root q=q ↔
      rootRepresentative g rows (faceRepresentative g hg rows R hr q).val=
        (faceRepresentative g hg rows R hr q).val := by
  constructor
  · intro h
    have hh:=congrArg (faceRepresentativeEquiv g hg rows R hr) h
    simp only [runtimeFaceRoots,Equiv.apply_symm_apply] at hh
    exact congrArg Subtype.val hh
  · intro h
    have hh:representativeRoot g rows (faceRepresentativeEquiv g hg rows R hr q)=
        faceRepresentativeEquiv g hg rows R hr q:=Subtype.ext h
    change (faceRepresentativeEquiv g hg rows R hr).symm _=q
    rw [hh,Equiv.symm_apply_apply]

end PlanarHom.PlanarityRowFaceCode

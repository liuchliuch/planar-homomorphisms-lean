import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.FisherExpansionCorrespondence
import Mathlib.Data.List.NodupEquivFin

/-! NEW literal bridge from a finite cyclic row to Fisher endpoint ordering.
Fisher's endpoint bit is the reverse of the Kasteleyn outward-dart bit. -/
noncomputable section
open Classical
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} {G : MultiGraph V E}

@[simp] theorem dartVertex_reverse (a : Dart E) : G.dartVertex (reversePerm E a)=(G.dartPair a).1 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

namespace PlanarityLRRealization.RotationRows
variable [DecidableEq (Dart E)] (R : RotationRows G)

 def incidenceOrdering : G.IncidenceOrdering where
  degree v := (R.row v).length
  atVertex v := (List.Nodup.getEquiv (R.row v) (R.nodup v)).trans
    { toFun := fun a=>⟨reversePerm E a.val,by rw [dartVertex_reverse]; exact (R.mem v a.val).mp a.property⟩
      invFun := fun a=>⟨reversePerm E a.val,by
        apply (R.mem v _).mpr
        have h := dartVertex_reverse (G:=G) (reversePerm E a.val)
        simp only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] at h
        exact h.symm.trans a.property⟩
      left_inv := by intro a; apply Subtype.ext; exact (reversePerm E).symm_apply_apply a.val
      right_inv := by intro a; apply Subtype.ext; exact (reversePerm E).symm_apply_apply a.val }

@[simp] theorem incidenceOrdering_degree (v : V) : R.incidenceOrdering.degree v=(R.row v).length := rfl

@[simp] theorem incidenceOrdering_darts (v : V) (i : Fin (R.row v).length) :
    R.incidenceOrdering.darts ⟨v,i⟩=reversePerm E ((R.row v).get i) := rfl

end PlanarityLRRealization.RotationRows

namespace MultiGraph.IncidenceOrdering
variable [DecidableEq (Dart E)] (o : G.IncidenceOrdering)

 def cyclicRow (v : V) : List (Dart E) := List.ofFn (fun i : Fin (o.degree v)=>reversePerm E (o.darts ⟨v,i⟩))

 theorem cyclicRow_nodup (v : V) : (o.cyclicRow v).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  have h := o.darts.injective ((reversePerm E).injective hij)
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

 theorem mem_cyclicRow (v : V) (a : Dart E) : a∈o.cyclicRow v ↔ (G.dartPair a).1=v := by
  rw [cyclicRow,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    have h := o.darts_vertex ⟨v,i⟩
    rw [←dartVertex_reverse (G:=G) (reversePerm E (o.darts ⟨v,i⟩))]
    simpa only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] using h
  · intro ha
    let b : G.VertexDarts v := ⟨reversePerm E a,by rw [dartVertex_reverse,ha]⟩
    let i := (o.atVertex v).symm b
    refine ⟨i,?_⟩
    have he := congrArg Subtype.val ((o.atVertex v).apply_symm_apply b)
    change o.darts ⟨v,i⟩=reversePerm E a at he
    rw [he]
    exact (reversePerm E).symm_apply_apply a

 def rotationRows : RotationRows G where
  row := o.cyclicRow
  nodup := o.cyclicRow_nodup
  mem := o.mem_cyclicRow

end MultiGraph.IncidenceOrdering

namespace PlanarityLRRealization.RotationRows
variable [DecidableEq (Dart E)] (R : RotationRows G)

@[simp] theorem incidenceOrdering_cyclicRow (v : V) : R.incidenceOrdering.cyclicRow v=R.row v := by
  change (List.ofFn (fun i : Fin (R.row v).length=>reversePerm E (reversePerm E ((R.row v).get i))))=R.row v
  have h : (fun i : Fin (R.row v).length=>reversePerm E (reversePerm E ((R.row v).get i)))=
      (fun i=>(R.row v).get i) := by funext i; exact (reversePerm E).symm_apply_apply _
  rw [h,List.ofFn_get]

 theorem incidenceOrdering_rotation : R.incidenceOrdering.rotationRows.rotation=R.rotation := by
  apply Equiv.ext
  intro a
  change (R.incidenceOrdering.cyclicRow (G.dartPair a).1).formPerm a=(R.row (G.dartPair a).1).formPerm a
  rw [R.incidenceOrdering_cyclicRow]

end PlanarityLRRealization.RotationRows
end PlanarHom

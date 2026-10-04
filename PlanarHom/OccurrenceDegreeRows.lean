import PlanarHom.FisherRotationOrdering

/-! NEW row completeness from exact occurrence degree, distinct named darts,
and their actual hosts. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} (G : MultiGraph V E)

 def hostDartEquiv (v : V) : {a : Dart E // (G.dartPair a).1=v}≃G.VertexDarts v where
  toFun a := ⟨reversePerm E a.val,by rw [dartVertex_reverse]; exact a.property⟩
  invFun a := ⟨reversePerm E a.val,by
    have h := dartVertex_reverse (G:=G) (reversePerm E a.val)
    simp only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] at h
    exact h.symm.trans a.property⟩
  left_inv a := by apply Subtype.ext; exact (reversePerm E).symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact (reversePerm E).symm_apply_apply a.val

 theorem host_card [Fintype E] (v : V) :
    Fintype.card {a : Dart E // (G.dartPair a).1=v}=G.selectedDegree Finset.univ v := by
  rw [Fintype.card_congr (G.hostDartEquiv v),G.degree_eq_dartCard]

 theorem row_mem_of_degree [Fintype E] [DecidableEq (Dart E)] (v : V) (xs : List (Dart E))
    (hn : xs.Nodup) (hh : ∀a∈xs,(G.dartPair a).1=v)
    (hl : xs.length=G.selectedDegree Finset.univ v) :
    ∀a : Dart E,a∈xs ↔ (G.dartPair a).1=v := by
  have hsub : xs.toFinset⊆Finset.univ.filter (fun a : Dart E=>(G.dartPair a).1=v) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh a (List.mem_toFinset.mp ha)⟩
  have hc : (Finset.univ.filter (fun a : Dart E=>(G.dartPair a).1=v)).card=G.selectedDegree Finset.univ v := by
    rw [←Fintype.card_subtype,G.host_card]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc,List.toFinset_card_of_nodup hn,hl])
  intro a
  rw [←List.mem_toFinset,heq]
  simp

end PlanarHom.MultiGraph

namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
theorem rotation_of_three (R : RotationRows G) (v : V) (a b c : Dart E)
    (hrow : R.row v=[a,b,c]) : R.rotation a=b ∧ R.rotation b=c ∧ R.rotation c=a := by
  have hn : [a,b,c].Nodup := hrow ▸ R.nodup v
  have ha : (G.dartPair a).1=v := (R.mem v a).mp (by rw [hrow]; simp)
  have hb : (G.dartPair b).1=v := (R.mem v b).mp (by rw [hrow]; simp)
  have hc : (G.dartPair c).1=v := (R.mem v c).mp (by rw [hrow]; simp)
  rw [R.rotation_apply a,R.rotation_apply b,R.rotation_apply c,ha,hb,hc,hrow]
  exact ⟨by simpa using List.formPerm_apply_getElem [a,b,c] hn 0 (by simp),
    by simpa using List.formPerm_apply_getElem [a,b,c] hn 1 (by simp),
    by simpa using List.formPerm_apply_getElem [a,b,c] hn 2 (by simp)⟩
end PlanarHom.PlanarityLRRealization.RotationRows

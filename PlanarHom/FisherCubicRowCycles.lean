import PlanarHom.FisherPolygonEuler
import PlanarHom.FisherTrianglePermutation

/-! NEW exact three-step cyclic row semantics for cubic Fisher decoration. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]

 private theorem list_three_cycle {A : Type*} [DecidableEq A]
    (xs : List A) (hn : xs.Nodup) (hl : xs.length=3) (a : A) (ha : a∈xs) :
    xs.formPerm^[3] a=a ∧ xs.formPerm a≠a ∧ xs.formPerm^[2] a≠a := by
  obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp hl
  have hx : [x,y,z].formPerm x=y := by
    simpa using (List.formPerm_apply_getElem [x,y,z] hn 0 (by simp))
  have hy : [x,y,z].formPerm y=z := by
    simpa using (List.formPerm_apply_getElem [x,y,z] hn 1 (by simp))
  have hz : [x,y,z].formPerm z=x := by
    simpa using (List.formPerm_apply_getElem [x,y,z] hn 2 (by simp))
  simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_nil,and_true,
    List.not_mem_nil,or_false] at hn ha
  rcases ha with rfl|rfl|rfl <;>
    simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,hx,hy,hz] <;> tauto

 theorem rotation_three (R : RotationRows G) (h3 : ∀v,(R.row v).length=3) (a : Dart E) :
    R.rotation^[3] a=a ∧ R.rotation a≠a ∧ R.rotation^[2] a≠a := by
  have h := list_three_cycle (R.row (G.dartPair a).1) (R.nodup _) (h3 _) a ((R.mem _ _).mpr rfl)
  rw [←R.rotation_iterate_eq_formPerm a 3,←R.rotation_iterate_eq_formPerm a 2] at h
  exact h

 theorem cubic_row_length [Fintype E] (p : (V×Fin 3)≃(E×Bool))
    (R : RotationRows (cubicOriginal p)) (v : V) : (R.row v).length=3 := by
  have hd := R.incidenceOrdering.degree_eq v
  change (R.row v).length=(cubicOriginal p).selectedDegree Finset.univ v at hd
  rw [hd,original_degree_eq_ports]
  simp [selectedPorts]

 def cubicVertexEquiv (p : (V×Fin 3)≃(E×Bool)) : Dart E≃V×Fin 3 :=
  (reversePerm E).trans p.symm

 theorem cubicVertexEquiv_host (p : (V×Fin 3)≃(E×Bool)) (a : Dart E) :
    (cubicVertexEquiv p a).1=((cubicOriginal p).dartPair a).1 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

 theorem cubicVertexEquiv_next_host (p : (V×Fin 3)≃(E×Bool))
    (R : RotationRows (cubicOriginal p)) (a : Dart E) :
    (cubicVertexEquiv p (R.rotation a)).1=(cubicVertexEquiv p a).1 := by
  rw [cubicVertexEquiv_host,R.rotation_host,cubicVertexEquiv_host]

 theorem cubicVertexEquiv_snd_ne (p : (V×Fin 3)≃(E×Bool)) (a b : Dart E)
    (hh : (cubicVertexEquiv p a).1=(cubicVertexEquiv p b).1) (hne : a≠b) :
    (cubicVertexEquiv p a).2≠(cubicVertexEquiv p b).2 := by
  intro h
  exact hne ((cubicVertexEquiv p).injective (Prod.ext hh h))

 theorem cubic_corner_endpoints [Fintype E] (p : (V×Fin 3)≃(E×Bool))
    (R : RotationRows (cubicOriginal p)) (a : Dart E) :
    let i:=cubicVertexEquiv p a
    let j:=cubicVertexEquiv p (R.rotation a)
    let k:=cubicVertexEquiv p (R.rotation (R.rotation a))
    (i.2=triangle.src k.2 ∧ j.2=triangle.dst k.2) ∨
      (i.2=triangle.dst k.2 ∧ j.2=triangle.src k.2) := by
  dsimp only
  have hn := rotation_three R (cubic_row_length p R) a
  have h2 : R.rotation (R.rotation a)≠a := by simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using hn.2.2
  apply triangle_other_pair
  · exact cubicVertexEquiv_snd_ne p _ _
      ((cubicVertexEquiv_next_host p R (R.rotation a)).trans (cubicVertexEquiv_next_host p R a)).symm h2.symm
  · exact cubicVertexEquiv_snd_ne p _ _ (cubicVertexEquiv_next_host p R (R.rotation a)).symm
      (fun h=>hn.2.1 (R.rotation.injective h).symm)
  · exact cubicVertexEquiv_snd_ne p _ _ (cubicVertexEquiv_next_host p R a).symm hn.2.1.symm

end PlanarHom.Fisher

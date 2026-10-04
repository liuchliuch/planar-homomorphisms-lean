import PlanarHom.RotationFaceCycleDuality
import PlanarHom.FinitePermutationCycleWords
import PlanarHom.FisherRotationOrdering
import PlanarHom.FinitePermutationCycleTransport

/-! NEW reconstruction of literal cyclic rows from a proved finite vertex
permutation. Endpoint-bit rotations are explicitly conjugated by reversal. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn FinitePermutationCycles FinitePermutationReturnWords
variable {V E : Type} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable [DecidableEq (Dart E)]

 theorem cycleWord_formPerm_on_cycle (P : Equiv.Perm (Dart E)) (a b : Dart E) (hb : b∈cycleWord P a) :
    (cycleWord P a).formPerm b=P b := by
  obtain ⟨i,hi,hix⟩:=List.mem_iff_getElem.mp hb
  rw [←hix,List.formPerm_apply_getElem _ (cycleWord_nodup P a) i hi]
  simp only [cycleWord,orbitPrefix,List.getElem_map,List.getElem_range,List.length_map,List.length_range]
  rw [Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']

 def ofHostPermutation (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1)
    (hinc : ∀v,∃a : Dart E,(G.dartPair a).1=v) : RotationRows G where
  row v:=cycleWord P (Classical.choose (hinc v))
  nodup v:=cycleWord_nodup P _
  mem v a:=by
    rw [mem_cycleWord,hcycles,Classical.choose_spec (hinc v),eq_comm]

 theorem ofHostPermutation_rotation (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1)
    (hinc : ∀v,∃a : Dart E,(G.dartPair a).1=v) :
    (ofHostPermutation P hcycles hinc).rotation=P := by
  apply Equiv.ext
  intro a
  change (cycleWord P (Classical.choose (hinc (G.dartPair a).1))).formPerm a=P a
  apply cycleWord_formPerm_on_cycle
  rw [mem_cycleWord,hcycles,Classical.choose_spec (hinc (G.dartPair a).1)]

 def endpointConjugate (P : Equiv.Perm (Dart E)) : Equiv.Perm (Dart E) :=
  (reversePerm E).permCongr P

 theorem endpointConjugate_step (P : Equiv.Perm (Dart E)) (a : Dart E) :
    reversePerm E (endpointConjugate P a)=P (reversePerm E a) := by
  change reversePerm E (reversePerm E (P (reversePerm E a)))=P (reversePerm E a)
  simp [reversePerm]

 theorem endpointConjugate_cycles (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ G.dartVertex a=G.dartVertex b) (a b : Dart E) :
    (endpointConjugate P).SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1 := by
  rw [sameCycle_iff_of_step _ P (reversePerm E) (endpointConjugate_step P) a b,
    hcycles,dartVertex_reverse,dartVertex_reverse]

 theorem endpoint_incident (hinc : Function.Surjective G.dartVertex) (v : V) :
    ∃a : Dart E,(G.dartPair a).1=v := by
  obtain ⟨a,ha⟩:=hinc v
  refine ⟨reversePerm E a,?_⟩
  have hh:=dartVertex_reverse (G:=G) (reversePerm E a)
  simp only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] at hh
  exact hh.symm.trans ha

 def ofEndpointPermutation (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hinc : Function.Surjective G.dartVertex) : RotationRows G :=
  ofHostPermutation (endpointConjugate P) (endpointConjugate_cycles P hcycles) (endpoint_incident hinc)

 theorem ofEndpointPermutation_rotation (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hinc : Function.Surjective G.dartVertex) :
    (ofEndpointPermutation P hcycles hinc).rotation=endpointConjugate P :=
  ofHostPermutation_rotation _ _ _

 theorem ofEndpointPermutation_face_reverse (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hinc : Function.Surjective G.dartVertex) (a : Dart E) :
    reversePerm E ((ofEndpointPermutation P hcycles hinc).facePerm a)=
      (P*reversePerm E) (reversePerm E a) := by
  change reversePerm E ((ofEndpointPermutation P hcycles hinc).rotation (reversePerm E a))=_
  rw [ofEndpointPermutation_rotation,endpointConjugate_step]
  rfl

 theorem ofEndpointPermutation_face_count (P : Equiv.Perm (Dart E))
    (hcycles : ∀a b,P.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hinc : Function.Surjective G.dartVertex) :
    count (ofEndpointPermutation P hcycles hinc).facePerm=count (P*reversePerm E) :=
  count_semiconj _ _ (reversePerm E) (ofEndpointPermutation_face_reverse P hcycles hinc)

end PlanarHom.PlanarityLRRealization.RotationRows

import PlanarHom.RotationFaceCycleDuality
import PlanarHom.OccurrenceMatchings

/-! NEW actual Boolean dual cuts for every even original occurrence subset at
the sphere Euler equality. The cut is derived from incidence exactness and
normalized to omit the designated face; no cut certificate is an input. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.MultiGraph
variable {V E : Type*} [Fintype V] [Fintype E]

def edgeIndicator (A : Finset E) (e : E) : ZMod 2 := by
  classical
  exact if e∈A then 1 else 0

theorem boundary_edgeIndicator (G : MultiGraph V E) (A : Finset E) (v : V) :
    (G.coboundaryMatrix (ZMod 2)).transpose.mulVec (edgeIndicator A) v=
      (G.selectedDegree A v : ZMod 2) := by
  classical
  simp [Matrix.mulVec,dotProduct,Matrix.transpose_apply,coboundaryMatrix,edgeIndicator,selectedDegree,
    mul_ite,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,Finset.sum_add_distrib]

theorem evenSubgraph_boundary_zero (G : MultiGraph V E) (A : Finset E) (hA : G.EvenSubgraph A) :
    (G.coboundaryMatrix (ZMod 2)).transpose.mulVec (edgeIndicator A)=0 := by
  funext v
  rw [G.boundary_edgeIndicator]
  exact ZMod.natCast_eq_zero_iff_even.mpr (hA v)

end PlanarHom.MultiGraph

namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

structure FaceCut (A : Finset E) (root : Dart E) where
  faceSide : R.Face → Bool
  root_false : faceSide (R.faceOf root)=false
  crosses : ∀ e, (faceSide (R.faceOf (e,true)) ^^ faceSide (R.faceOf (e,false))) = decide (e∈A)

private theorem zmod2_cut_xor (x y : ZMod 2) (p : Prop) [Decidable p]
    (h : x-y=if p then 1 else 0) : (decide (x=1) ^^ decide (y=1))=decide p := by
  fin_cases x <;> fin_cases y <;> by_cases hp : p <;> norm_num [hp] at *

/-- Genuine cut existence for every even edge subset of the actual rotation.
The arbitrary omitted face lies on the false side by construction. -/
theorem exists_faceCut (root : Dart E) (hG : ∀ u v, G.componentSetoid Finset.univ u v)
    (heuler : Fintype.card V+Fintype.card R.Face=Fintype.card E+2)
    (A : Finset E) (hA : G.EvenSubgraph A) : Nonempty (R.FaceCut A root) := by
  classical
  obtain ⟨f,hroot,hf⟩ := R.exists_face_potential root hG heuler (edgeIndicator A) (G.evenSubgraph_boundary_zero A hA)
  refine ⟨⟨fun F => decide (f F=1),by simp [hroot],?_⟩⟩
  intro e
  exact zmod2_cut_xor _ _ (e∈A) (hf e)

namespace FaceCut
variable {R} {A : Finset E} {root : Dart E} (C : R.FaceCut A root)

def side (a : Dart E) : Bool := C.faceSide (R.faceOf a)

@[simp] theorem side_facePerm (a : Dart E) : C.side (R.facePerm a)=C.side a := by
  simp only [side,R.faceOf_facePerm]

theorem side_rotation (a : Dart E) : C.side (R.rotation a)=C.side (reversePerm E a) := by
  simp only [side,R.faceOf_rotation]

theorem crosses_dart (a : Dart E) : (C.side a ^^ C.side (reversePerm E a))=decide (a.1∈A) := by
  rcases a with ⟨e,b⟩
  cases b
  · simpa only [side,reversePerm,Equiv.coe_fn_mk,Bool.not_false,Bool.xor_comm] using C.crosses e
  · exact C.crosses e

theorem rotation_crosses (a : Dart E) : (C.side a ^^ C.side (R.rotation a))=decide (a.1∈A) := by
  rw [C.side_rotation]
  exact C.crosses_dart a

theorem side_reverse_of_notMem (a : Dart E) (ha : a.1∉A) : C.side (reversePerm E a)=C.side a := by
  have hh := C.crosses_dart a
  simp only [decide_eq_false ha] at hh
  cases h₁ : C.side a <;> cases h₂ : C.side (reversePerm E a) <;> simp_all

theorem side_rotation_of_notMem (a : Dart E) (ha : a.1∉A) : C.side (R.rotation a)=C.side a := by
  rw [C.side_rotation,C.side_reverse_of_notMem a ha]

/-- Away from boundary incidences, all corners at one original vertex have
the same derived face color. -/
theorem vertex_constant {v : V} (hv : ∀ a : Dart E, (G.dartPair a).1=v → a.1∉A)
    (a b : Dart E) (ha : (G.dartPair a).1=v) (hb : (G.dartPair b).1=v) : C.side a=C.side b := by
  obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b (ha.trans hb.symm)
  have hi : ∀ n, C.side (R.rotation^[n] a)=C.side a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',C.side_rotation_of_notMem _ (hv _ (by rw [R.rotation_iterate_host,ha])),ih]
  exact (hi n).symm.trans (congrArg C.side hn)

def InsideVertex (v : V) : Prop := ∀ a : Dart E, (G.dartPair a).1=v → C.side a=true

theorem inside_excludes_boundary {v : V} (hv : C.InsideVertex v)
    (a : Dart E) (ha : (G.dartPair a).1=v) : a.1∉A := by
  intro hm
  have hh := C.rotation_crosses a
  rw [hv a ha,hv (R.rotation a) (by rw [R.rotation_host,ha]),decide_eq_true hm] at hh
  contradiction

theorem inside_iff_across_nonboundary (e : E) (he : e∉A)
    (hs : ∀ a : Dart E, (G.dartPair a).1=G.src e → a.1∉A)
    (ht : ∀ a : Dart E, (G.dartPair a).1=G.dst e → a.1∉A) :
    C.InsideVertex (G.src e) ↔ C.InsideVertex (G.dst e) := by
  have hrev : C.side (e,false)=C.side (e,true) := C.side_reverse_of_notMem (e,true) he
  constructor
  · intro h b hb
    exact (C.vertex_constant ht b (e,false) hb rfl).trans (hrev.trans (h (e,true) rfl))
  · intro h b hb
    exact (C.vertex_constant hs b (e,true) hb rfl).trans (hrev.symm.trans (h (e,false) rfl))

end FaceCut
end PlanarHom.PlanarityLRRealization.RotationRows

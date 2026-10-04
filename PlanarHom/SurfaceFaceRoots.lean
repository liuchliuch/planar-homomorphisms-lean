import PlanarHom.SurfaceNullCycleSigns
import PlanarHom.RotationFaceCutSigns

/-! NEW componentwise normalization of null face potentials. A root selector
is constant across every dual edge and idempotent. It is constructed from the
actual runtime omitted faces, not supplied as a sign certificate. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

structure FaceRoots where
  root : R.Face→R.Face
  idempotent : ∀q,root (root q)=root q
  across : ∀e,root (R.faceOf (e,true))=root (R.faceOf (e,false))

namespace FaceRoots
variable {R} (S : R.FaceRoots)

def normalize (f : R.Face→ZMod 2) : R.Face→ZMod 2 := fun q=>f q-f (S.root q)

@[simp] theorem normalize_root (f : R.Face→ZMod 2) (q : R.Face) : S.normalize f (S.root q)=0 := by
  simp [normalize,S.idempotent]

theorem boundary_normalize (f : R.Face→ZMod 2) :
    (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec (S.normalize f)=
      (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec f := by
  funext e
  rw [R.dualGraph.coboundaryMatrix_apply,R.dualGraph.coboundaryMatrix_apply]
  change (f (R.faceOf (e,true))-f (S.root (R.faceOf (e,true))))-
    (f (R.faceOf (e,false))-f (S.root (R.faceOf (e,false))))=f (R.faceOf (e,true))-f (R.faceOf (e,false))
  rw [S.across]
  ring

/-- Every omitted root is outside the derived cut, simultaneously. -/
theorem exists_faceCut_of_null [Nonempty E] (A : Finset E) (hA : G.EvenSubgraph A)
    (hnull : R.homologyClass (R.evenSubgraphCycle A hA)=0) :
    ∃root : Dart E,∃C : R.FaceCut A root,∀q,S.root q=q→C.faceSide q=false := by
  obtain ⟨f,hf⟩:=(R.homologyClass_eq_zero_iff (R.evenSubgraphCycle A hA)).mp hnull
  let q:=S.root (R.faceOf (Classical.arbitrary E,true))
  obtain ⟨a,ha⟩:=Quotient.exists_rep q
  have ha' : R.faceOf a=q:=ha
  have hz:S.normalize f (R.faceOf a)=0:=by rw [ha']; exact S.normalize_root f _
  have hf':(R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec (S.normalize f)=edgeIndicator A :=
    (S.boundary_normalize f).trans hf
  refine ⟨a,{faceSide:=fun q=>decide (S.normalize f q=1),root_false:=by simp [hz],crosses:=?_},?_⟩
  · intro e
    have he:=congrFun hf' e
    rw [R.dualGraph.coboundaryMatrix_apply] at he
    change S.normalize f (R.faceOf (e,true))-S.normalize f (R.faceOf (e,false))=if e∈A then 1 else 0 at he
    change (decide (S.normalize f (R.faceOf (e,true))=1) ^^ decide (S.normalize f (R.faceOf (e,false))=1))=decide (e∈A)
    generalize hx:S.normalize f (R.faceOf (e,true))=x at he ⊢
    generalize hy:S.normalize f (R.faceOf (e,false))=y at he ⊢
    fin_cases x <;> fin_cases y <;> by_cases heA:e∈A <;> norm_num [heA] at *
  · intro q hq
    change decide (S.normalize f q=1)=false
    have hzero:S.normalize f q=0:=by rw [←hq]; exact S.normalize_root f q
    simp [hzero]

end FaceRoots
namespace FaceCut
variable {R} {A : Finset E} {root : Dart E} (C : R.FaceCut A root)

theorem selectedFace_productLaw_of_roots (S : R.FaceRoots)
    (hzero : ∀q,S.root q=q→C.faceSide q=false) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,S.root q≠q→
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1)) :
    FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val) := by
  unfold selectedFace
  refine FinitePermutationCycles.cycleProductLaw_subtype R.facePerm (dartSign orientation)
    (fun a=>C.side a=true) (fun a=>by change C.side (R.facePerm a)=true↔C.side a=true; rw [C.side_facePerm]) ?_
  intro q hq
  apply hfaces q
  intro he
  obtain ⟨a,ha,hclass⟩:=hq
  have hs:C.side a=false:=by
    change C.faceSide (R.faceOf a)=false
    change R.faceOf a=q at hclass
    rw [hclass]
    exact hzero q he
  rw [hs] at ha
  contradiction

end FaceCut
end PlanarHom.PlanarityLRRealization.RotationRows

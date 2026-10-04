import PlanarHom.FiniteGraphCycleDuality
import PlanarHom.PlanarityLRDualReachability
import Mathlib.Algebra.Field.ZMod

/-! NEW actual rotation-face incidence exactness. Faces are precisely quotient
cycles of reversal followed by the literal vertex rotation. Both boundary
compatibility and dual connectivity are proved from these permutations. -/
noncomputable section
open scoped BigOperators
open Matrix Module
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

def facePerm : Equiv.Perm (Dart E) := (reversePerm E).trans R.rotation
abbrev Face := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

instance faceFintype : Fintype R.Face := Fintype.ofFinite _

def faceOf (a : Dart E) : R.Face := Quotient.mk _ a

@[simp] theorem faceOf_facePerm (a : Dart E) : R.faceOf (R.facePerm a)=R.faceOf a :=
  Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left

theorem facePerm_host (a : Dart E) : (G.dartPair (R.facePerm a)).1=(G.dartPair (reversePerm E a)).1 :=
  R.rotation_host _

theorem faceOf_rotation (a : Dart E) : R.faceOf (R.rotation a)=R.faceOf (reversePerm E a) := by
  have hh := R.faceOf_facePerm (reversePerm E a)
  simpa only [facePerm,Equiv.trans_apply,reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] using hh

def dualGraph : MultiGraph R.Face E where
  src e := R.faceOf (e,true)
  dst e := R.faceOf (e,false)

theorem cycleDualCompatible [Field K] : CycleDualCompatible (K:=K) G R.dualGraph := by
  classical
  ext v f
  let weight (a : Dart E) : K := (if (G.dartPair a).1=v then 1 else 0)*(if R.faceOf a=f then 1 else 0)
  have hs : (∑ a : Dart E, weight (R.facePerm a))=∑ a : Dart E, weight a :=
    Equiv.sum_comp R.facePerm weight
  calc
    ((G.coboundaryMatrix K).transpose * R.dualGraph.coboundaryMatrix K) v f =
        ∑ e : E, ((weight (e,true)+weight (e,false))-
          (weight (R.facePerm (e,true))+weight (R.facePerm (e,false)))) := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply,coboundaryMatrix,dualGraph]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [weight]
      rw [R.facePerm_host,R.facePerm_host,R.faceOf_facePerm,R.faceOf_facePerm]
      simp only [reversePerm,Equiv.coe_fn_mk,dartPair,Bool.not_true,Bool.not_false,if_true,Bool.false_eq_true,if_false]
      ring
    _ = (∑ a : Dart E, weight a)-(∑ a : Dart E, weight (R.facePerm a)) := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_sub_distrib]
    _ = 0 := by rw [hs,sub_self]

theorem dual_connected_reverse (a : Dart E) :
    R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf (reversePerm E a)) := by
  rcases a with ⟨e,b⟩
  have hh : R.dualGraph.componentSetoid Finset.univ (R.faceOf (e,true)) (R.faceOf (e,false)) :=
    Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
  cases b
  · exact hh.symm
  · exact hh

theorem dual_connected_sameHost (a b : Dart E) (hab : (G.dartPair a).1=(G.dartPair b).1) :
    R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf b) := by
  obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b hab
  have hs (x : Dart E) : R.dualGraph.componentSetoid Finset.univ (R.faceOf x) (R.faceOf (R.rotation x)) := by
    rw [R.faceOf_rotation]
    exact R.dual_connected_reverse x
  have hi : ∀ n, R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf (R.rotation^[n] a)) := by
    intro n
    induction n with
    | zero => exact Relation.EqvGen.refl _
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.EqvGen.trans _ _ _ ih (hs _)
  simpa only [hn] using hi n

/-- Connectivity of the literal dual is a consequence of ordinary primal
connectivity and each host's proved full cyclic row. -/
theorem dualGraph_connected (hG : ∀ u v, G.componentSetoid Finset.univ u v) :
    ∀ f g, R.dualGraph.componentSetoid Finset.univ f g := by
  intro f g
  induction f using Quotient.inductionOn with
  | h a =>
    induction g using Quotient.inductionOn with
    | h b =>
      have hinc : ∀ v, ∃ c : Dart E, (G.dartPair c).1=v := by
        intro v
        let incident (u : V) : Prop := ∃ c : Dart E, (G.dartPair c).1=u
        have hc : G.EdgeConstant Finset.univ incident := by
          intro e he
          apply propext
          exact ⟨fun _ => ⟨(e,false),rfl⟩,fun _ => ⟨(e,true),rfl⟩⟩
        have hh := G.edgeConstant_respects Finset.univ incident hc (hG (G.dartPair a).1 v)
        change incident v
        exact Eq.mp hh ⟨a,rfl⟩
      have lift : ∀ u v, G.componentSetoid Finset.univ u v →
          ∀ a b : Dart E, (G.dartPair a).1=u → (G.dartPair b).1=v →
            R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf b) := by
        intro u v huv
        induction huv with
        | rel u v h =>
          obtain ⟨e,_,rfl,rfl⟩ := h
          intro a b ha hb
          exact Relation.EqvGen.trans _ _ _ (R.dual_connected_sameHost a (e,true) ha)
            (Relation.EqvGen.trans _ _ _ (R.dual_connected_reverse (e,true)) (R.dual_connected_sameHost (e,false) b hb.symm))
        | refl u =>
          intro a b ha hb
          exact R.dual_connected_sameHost a b (ha.trans hb.symm)
        | symm u v h ih =>
          intro a b ha hb
          exact (ih b a hb ha).symm
        | trans u v w h₁ h₂ ih₁ ih₂ =>
          intro a b ha hb
          obtain ⟨c,hc⟩ := hinc v
          exact Relation.EqvGen.trans _ _ _ (ih₁ a c ha hc) (ih₂ c b hc hb)
      exact lift _ _ (hG _ _) a b rfl rfl

theorem euler_le (root : Dart E) (hG : ∀ u v, G.componentSetoid Finset.univ u v) :
    Fintype.card V+Fintype.card R.Face≤Fintype.card E+2 :=
  G.cycleDual_euler_le (K:=ZMod 2) R.dualGraph (G.dartPair root).1 (R.faceOf root)
    hG (R.dualGraph_connected hG) R.cycleDualCompatible

/-- At the proved Euler equality, every actual closed primal edge chain has a
face potential vanishing on the requested omitted face. This is the genuine
finite dual-cut existence theorem required by Kasteleyn parity. -/
theorem exists_face_potential (root : Dart E) (hG : ∀ u v, G.componentSetoid Finset.univ u v)
    (heuler : Fintype.card V+Fintype.card R.Face=Fintype.card E+2)
    (cycle : E → ZMod 2) (hcycle : (G.coboundaryMatrix (ZMod 2)).transpose.mulVec cycle=0) :
    ∃ f : R.Face → ZMod 2, f (R.faceOf root)=0 ∧
      ∀ e, f (R.faceOf (e,true))-f (R.faceOf (e,false))=cycle e := by
  obtain ⟨f,hf,h⟩ := G.exists_normalized_dual_potential R.dualGraph (G.dartPair root).1 (R.faceOf root)
    hG (R.dualGraph_connected hG) R.cycleDualCompatible heuler cycle hcycle
  refine ⟨f,hf,?_⟩
  intro e
  have hh := congrFun h e
  rw [R.dualGraph.coboundaryMatrix_apply] at hh
  exact hh

end PlanarHom.PlanarityLRRealization.RotationRows

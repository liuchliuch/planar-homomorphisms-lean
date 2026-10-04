import PlanarHom.SurfaceRotationHomology
import PlanarHom.RotationDartRelabel

/-! NEW endpoint-direction independent F2 chain boundary and genuine dart
relabeling transport. This handles reflected cubic port enumerations exactly. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E]

theorem chainBoundary_eq_dartSum (G : MultiGraph V E) (z : E→ZMod 2) (v : V) :
    (G.coboundaryMatrix (ZMod 2)).transpose.mulVec z v=
      ∑a : Dart E,if (G.dartPair a).1=v then z a.1 else 0 := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,coboundaryMatrix,
    Fintype.sum_prod_type,Fintype.sum_bool,dartPair,if_true,Bool.false_eq_true,if_false,
    sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_mul,ite_mul,one_mul,zero_mul]

namespace DartRelabel
variable {W F : Type*} [Fintype W] [Fintype F]
variable {G : MultiGraph V E} {H : MultiGraph W F} (e : DartRelabel G H)

def pullEdgeVector (z : F→ZMod 2) : E→ZMod 2 := fun a=>z (e.dart (a,true)).1

theorem pullEdgeVector_dart (z : F→ZMod 2) (a : Dart E) :
    e.pullEdgeVector z a.1=z (e.dart a).1 := by
  rcases a with ⟨a,b⟩
  cases b
  · have hh:=congrArg Prod.fst (e.reverse (a,true))
    change (e.dart (a,false)).1=(e.dart (a,true)).1 at hh
    exact congrArg z hh.symm
  · rfl

theorem pullEdgeVector_boundary (z : F→ZMod 2) (v : V) :
    (G.coboundaryMatrix (ZMod 2)).transpose.mulVec (e.pullEdgeVector z) v=
      (H.coboundaryMatrix (ZMod 2)).transpose.mulVec z (e.vertex v) := by
  rw [chainBoundary_eq_dartSum,chainBoundary_eq_dartSum]
  calc
    _ = ∑a : Dart E,if (H.dartPair (e.dart a)).1=e.vertex v then z (e.dart a).1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [e.host,e.vertex.injective.eq_iff,e.pullEdgeVector_dart]
    _ = _ := Equiv.sum_comp e.dart (fun a : Dart F=>if (H.dartPair a).1=e.vertex v then z a.1 else 0)

variable [DecidableEq (Dart E)] [DecidableEq (Dart F)] (R : RotationRows G)

def pullCycle (c : (e.rows R).cycleSpace) : R.cycleSpace := by
  refine ⟨e.pullEdgeVector c.val,?_⟩
  change (G.coboundaryMatrix (ZMod 2)).transpose.mulVec (e.pullEdgeVector c.val)=0
  funext v
  rw [e.pullEdgeVector_boundary]
  exact congrFun c.property (e.vertex v)

end DartRelabel
end PlanarHom.MultiGraph

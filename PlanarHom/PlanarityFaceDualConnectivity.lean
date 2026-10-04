import PlanarHom.PlanarityFaceDualData
import PlanarHom.PlanarityLRDualReachability
import PlanarHom.PlanarityFaceRoots

/-! NEW instantiation of actual dart/DFS connectivity for the literal numeric
face labels and two-sided dual data; dual reachability is proved, not assumed. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization

 theorem faceId_facePermutation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : MultiGraph.Kasteleyn.Dart (Fin g.edges.length)) :
    faceId g bits (eraseDart (facePermutation g hg bits a))=faceId g bits (eraseDart a) := by
  unfold faceId
  congr 1
  exact representative_eq_of_sameCycle g hg bits _ a Equiv.Perm.SameCycle.rfl.apply_left

 theorem dualData_adj_reverse (g : MixedCode) (bits : List Bool)
    (a : MultiGraph.Kasteleyn.Dart (Fin g.edges.length)) :
    (dualData g bits).Adj (faceId g bits (eraseDart a))
      (faceId g bits (eraseDart (reversePerm _ a))) := by
  refine ⟨a.1.val,?_⟩
  rw [dualData_left g bits a.1.isLt,dualData_right g bits a.1.isLt]
  rcases a with ⟨e,b⟩
  cases b <;> simp [eraseDart,reversePerm]

 theorem dualData_reachable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a b : Dart} (ha : a.1<g.edges.length) (hb : b.1<g.edges.length)
    (hr : componentRoot g (host g a)=componentRoot g (host g b)) :
    Relation.ReflTransGen (dualData g bits).Adj (faceId g bits a) (faceId g bits b) := by
  have hh:=dualReachable_of_componentRoot_eq g hg bits
    (fun a=>faceId g bits (eraseDart a)) (dualData g bits).Adj
    (faceId_facePermutation g hg bits) (dualData_adj_reverse g bits)
    (liftDart a ha) (liftDart b hb) hr
  simpa only [erase_liftDart] using hh

 theorem selectedRoot_reachable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a∈representatives g bits) :
    Relation.ReflTransGen (dualData g bits).Adj
      (faceId g bits (rootRepresentative g bits a)) (faceId g bits a) :=
   dualData_reachable g hg bits
     (representative_index_of_mem g bits (rootRepresentative_mem g bits ha))
     (representative_index_of_mem g bits ha) (rootRepresentative_component g bits ha)

end PlanarHom.PlanarityFaceCode

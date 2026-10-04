import PlanarHom.PlanarityRowFaceDualData
import PlanarHom.PlanarityRowDualReachability
import PlanarHom.PlanarityRowFaceRoots

/-! NEW instantiation of actual dart/DFS connectivity for the literal numeric
face labels and two-sided dual data; dual reachability is proved, not assumed. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization

 theorem faceId_facePermutation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : MultiGraph.Kasteleyn.Dart (Fin g.edges.length)) :
    faceId g rows (eraseDart (R.facePerm a))=faceId g rows (eraseDart a) := by
  unfold faceId
  congr 1
  exact representative_eq_of_sameCycle g hg rows R hrows _ a Equiv.Perm.SameCycle.rfl.apply_left

 theorem dualData_adj_reverse (g : MixedCode) (rows : Rows)
    (a : MultiGraph.Kasteleyn.Dart (Fin g.edges.length)) :
    (dualData g rows).Adj (faceId g rows (eraseDart a))
      (faceId g rows (eraseDart (reversePerm _ a))) := by
  refine ⟨a.1.val,?_⟩
  rw [dualData_left g rows a.1.isLt,dualData_right g rows a.1.isLt]
  rcases a with ⟨e,b⟩
  cases b <;> simp [eraseDart,reversePerm]

 theorem dualData_reachable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) {a b : Dart} (ha : a.1<g.edges.length) (hb : b.1<g.edges.length)
    (hr : componentRoot g (host g a)=componentRoot g (host g b)) :
    Relation.ReflTransGen (dualData g rows).Adj (faceId g rows a) (faceId g rows b) := by
  have hh:=dualReachable_of_componentRoot_eq g hg R
    (fun a=>faceId g rows (eraseDart a)) (dualData g rows).Adj
    (faceId_facePermutation g hg rows R hrows) (dualData_adj_reverse g rows)
    (liftDart a ha) (liftDart b hb) hr
  simpa only [erase_liftDart] using hh

 theorem selectedRoot_reachable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) {a : Dart} (ha : a∈representatives g rows) :
    Relation.ReflTransGen (dualData g rows).Adj
      (faceId g rows (rootRepresentative g rows a)) (faceId g rows a) :=
   dualData_reachable g hg rows R hrows
     (representative_index_of_mem g rows (rootRepresentative_mem g rows ha))
     (representative_index_of_mem g rows ha) (rootRepresentative_component g rows ha)

end PlanarHom.PlanarityRowFaceCode

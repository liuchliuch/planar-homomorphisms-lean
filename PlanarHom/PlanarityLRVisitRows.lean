import PlanarHom.PlanarityLRForwardRows

/-! NEW linearized local contour rows: a nonroot parent dart closes its row.
This is a cyclic rotation of the actual computed row, with the same permutation. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
local instance visitRowsDartBEq : BEq Dart := instBEqOfDecidableEq

 def visitRow (g : MixedCode) (bits : List Bool) (v : ℕ) : List Dart :=
   ((orderedOutgoing g bits v).flatMap (edgeBlock g bits)++loopRow g v)++parentRow g v
 def rowIndex (row : List Dart) (a : Dart) : ℕ := @List.idxOf Dart instBEqOfDecidableEq a row
 def localRank (g : MixedCode) (bits : List Bool) (v : ℕ) (a : Dart) : ℕ := rowIndex (visitRow g bits v) a

 theorem visitRow_root (g : MixedCode) (bits : List Bool) {v : ℕ} (hz : height g v=0) :
    visitRow g bits v=directRow g bits v := by simp [visitRow,directRow,parentRow,hz]

 theorem visitRow_rotate (g : MixedCode) (bits : List Bool) {v : ℕ} (hz : height g v≠0) :
    visitRow g bits v=(directRow g bits v).rotate 1 := by
  simp [visitRow,directRow,parentRow,hz,List.rotate_cons_succ]

 theorem visitRow_perm (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (visitRow g bits v).Perm (directRow g bits v) := by
  by_cases hz:height g v=0
  · rw [visitRow_root g bits hz]
  · rw [visitRow_rotate g bits hz]
    exact List.rotate_perm _ _

 theorem visitRow_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) : (visitRow g bits v).Nodup :=
   (visitRow_perm g bits v).symm.nodup (directRow_nodup g hg bits hv)

 theorem visitRow_formPerm (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) :
    (visitRow g bits v).formPerm=(directRow g bits v).formPerm := by
  by_cases hz:height g v=0
  · rw [visitRow_root g bits hz]
  · rw [visitRow_rotate g bits hz]
    exact List.formPerm_rotate _ (directRow_nodup g hg bits hv) _

 theorem mem_visitRow (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) (a : Dart) :
    a∈visitRow g bits v ↔ a.1<g.edges.length ∧ host g a=v := by
  rw [(visitRow_perm g bits v).mem_iff,mem_directRow g hg bits hv]

 theorem visitRow_filter_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : ℕ) :
    (visitRow g bits v).filter (forwardFlag g)=(orderedOutgoing g bits v).map (outward g) := by
  have h:=directRow_filter_forward g hg bits v
  simpa only [visitRow,directRow,List.filter_append,parentRow_filter_forward,
    List.nil_append,List.append_nil] using h

 theorem visitRow_parent_last (g : MixedCode) (bits : List Bool) {v : ℕ} (hp : 0<height g v) :
    visitRow g bits v=((orderedOutgoing g bits v).flatMap (edgeBlock g bits)++loopRow g v)++
      [reverse (outward g (parentEdge g v))] := by
  simp [visitRow,parentRow,show height g v≠0 by omega]

 theorem localRank_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) {a : Dart}
    (ha : a.1<g.edges.length) (hhost : host g a=v) : localRank g bits v a<(visitRow g bits v).length :=
   List.idxOf_lt_length_of_mem ((mem_visitRow g hg bits hv a).mpr ⟨ha,hhost⟩)

end PlanarHom.PlanarityLRDirect

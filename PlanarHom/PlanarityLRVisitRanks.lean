import PlanarHom.PlanarityLRVisitRows

/-! NEW exact local contour ranks for the actual cyclic row permutation. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
local instance visitRanksDartBEq : BEq Dart := instBEqOfDecidableEq

 theorem rowIndex_formPerm (row : List Dart) (hn : row.Nodup) {a : Dart} (ha : a∈row) :
    rowIndex row (row.formPerm a)=(rowIndex row a+1)%row.length := by
  have hi : rowIndex row a<row.length:=List.idxOf_lt_length_of_mem ha
  have he : row[rowIndex row a]=a:=List.getElem_idxOf hi
  have hm : (rowIndex row a+1)%row.length<row.length:=Nat.mod_lt _ (by omega)
  have hf:=List.formPerm_apply_getElem row hn (rowIndex row a) hi
  rw [he] at hf
  rw [hf]
  exact List.idxOf_getElem hn _ hm

 theorem directRotation_eq_visitRow_formPerm (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    directRotation g bits a=(visitRow g bits (host g a)).formPerm a := by
  have hv:=host_valid g hg ha
  have hm: a∈directRow g bits (host g a):=(mem_directRow g hg bits hv a).mpr ⟨ha,rfl⟩
  rw [directRotation,PlanarityLRRealization.rowNext_eq_formPerm _ (directRow_nodup g hg bits hv) a hm,
    visitRow_formPerm g hg bits hv]

 theorem localRank_directRotation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    localRank g bits (host g a) (directRotation g bits a)=
      (localRank g bits (host g a) a+1)%(visitRow g bits (host g a)).length := by
  rw [directRotation_eq_visitRow_formPerm g hg bits ha]
  exact rowIndex_formPerm _ (visitRow_nodup g hg bits (host_valid g hg ha))
    ((mem_visitRow g hg bits (host_valid g hg ha) a).mpr ⟨ha,rfl⟩)

 theorem rowIndex_last (row : List Dart) (a : Dart) (hn : (row++[a]).Nodup) :
    rowIndex (row++[a]) a=row.length := by
  have hh:=List.idxOf_getElem hn row.length (by simp)
  simpa only [List.getElem_concat_length rfl] using hh

 theorem localRank_parent_last (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) (hp : 0<height g v) :
    localRank g bits v (reverse (outward g (parentEdge g v)))+1=(visitRow g bits v).length := by
  have hn:=visitRow_nodup g hg bits hv
  rw [visitRow_parent_last g bits hp] at hn
  unfold localRank
  rw [visitRow_parent_last g bits hp,rowIndex_last _ _ hn]
  simp [Nat.add_assoc]

 theorem rowIndex_eq_zero_iff (row : List Dart) {a : Dart} (ha : a∈row) :
    rowIndex row a=0 ↔ row.head?=some a := by
  cases row with
  | nil => simp at ha
  | cons b bs =>
    simp only [rowIndex,List.idxOf_cons,List.head?_cons,Option.some.injEq]
    by_cases hab:b=a
    · simp [hab]
    · simp [hab,Bool.beq_eq_decide_eq]

end PlanarHom.PlanarityLRDirect

import PlanarHom.RepresentedPowerTable
import Mathlib.Data.List.OfFn

noncomputable section
open Classical
namespace PlanarHom.RepresentedPowerTable
open RepresentedBit
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ} {A B:Fin t→K}

def sourceNode (rs:List (Row P t)) (i:Fin rs.length) : K := source P (rs.get i)
def targetNode (rs:List (Row P t)) (i:Fin rs.length) : K := target P (rs.get i)

theorem table_pairwise (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) :
    (table P E WA WB m).Pairwise (fun r s=>source P r≠source P s) := by
  have h:=ExponentProductTables.representatives_pairwise A B m
  rw [←table_semantics P E WA WB m,List.pairwise_map] at h
  exact h

theorem table_source_nonzero (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B)
    (m:ℕ) (r:Row P t) (hr:r∈table P E WA WB m) : source P r≠0 := by
  have hm:(source P r,target P r)∈(table P E WA WB m).map (fun r=>(source P r,target P r)):=
    List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [table_semantics] at hm
  exact ExponentProductTables.representatives_nonzero A B m _ hm

theorem table_sourceNode_injective (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) : Function.Injective (sourceNode P (table P E WA WB m)) := by
  intro i j hij
  have hp:=List.pairwise_iff_get.mp (table_pairwise P E WA WB m)
  by_contra hne
  have hv:i.val≠j.val:=fun h=>hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hl|hg
  · exact hp i j hl hij
  · exact hp j i hg hij.symm

theorem table_sourceNode_nonzero (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) (i:Fin (table P E WA WB m).length) :
    sourceNode P (table P E WA WB m) i≠0 :=
  table_source_nonzero P E WA WB m _ (List.get_mem _ i)

end PlanarHom.RepresentedPowerTable

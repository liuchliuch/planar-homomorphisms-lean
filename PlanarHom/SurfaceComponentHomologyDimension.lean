import PlanarHom.SurfaceHomologyCountTransport

/-! NEW exact additivity and restriction bound for the actual computed DFS
component rotations, including zero-dart isolated components. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRawEmbedding
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open Module
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (R : RotationRows (g.toMultiGraph hg))

theorem homology_finrank_eq_totalGenus :
    finrank (ZMod 2) R.Homology=2*totalGenus g hg R := by
  have ha:=global_capped_euler g hg R
  have hb:=R.homology_finrank_ribbon_euler
  simp only [Fintype.card_fin] at hb
  omega

theorem component_homology_finrank (r : Root g) :
    finrank (ZMod 2) (componentRows g hg r.val.val R).Homology=2*componentGenus g hg R r := by
  by_cases he:IsEmpty (ComponentEdge g r.val.val)
  · letI:=he
    haveI : Subsingleton (componentRows g hg r.val.val R).cycleSpace:=inferInstance
    have hz:finrank (ZMod 2) (componentRows g hg r.val.val R).cycleSpace=0:=finrank_zero_of_subsingleton
    have hq:=(componentRows g hg r.val.val R).faceBoundariesInCycles.finrank_quotient_add_finrank
    change finrank (ZMod 2) (componentRows g hg r.val.val R).Homology+_= _ at hq
    rw [hz] at hq
    simp only [componentGenus,if_pos he,mul_zero]
    omega
  · letI : Nonempty (ComponentEdge g r.val.val):=not_isEmpty_iff.mp he
    exact (componentRows g hg r.val.val R).homology_finrank_of_genus
      (Classical.choice inferInstance,true) (componentGraph_connected g hg r.val r.property)
      (componentGenus_hasGenus g hg R r)

theorem component_homology_finrank_le (r : Root g) :
    finrank (ZMod 2) (componentRows g hg r.val.val R).Homology≤finrank (ZMod 2) R.Homology := by
  rw [component_homology_finrank,homology_finrank_eq_totalGenus]
  apply Nat.mul_le_mul_left
  exact Finset.single_le_sum (fun i (_:i∈(Finset.univ:Finset (Root g)))=>Nat.zero_le _)
    (Finset.mem_univ r)

end PlanarHom.SurfaceRawEmbedding

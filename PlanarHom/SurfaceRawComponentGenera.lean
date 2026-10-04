import PlanarHom.SurfaceRotationGenus
import PlanarHom.SurfaceComplementGenusBound
import PlanarHom.PlanarityLRIsolatedRoots
import PlanarHom.PlanarityLRComponentConnected

/-! NEW actual component genus extraction for supplied raw rotation rows.
Isolated vertices contribute one ribbon boundary and genus zero. -/
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 200000
namespace PlanarHom.SurfaceRawEmbedding
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization
open FinitePermutationCycles SurfaceRibbonComplement

 def componentGenus (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (r : Root g) : ℕ :=
  if IsEmpty (ComponentEdge g r.val.val) then 0
  else SurfaceRotationGenus.genus (componentRows g hg r.val.val R)

 def totalGenus (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) : ℕ := ∑r:Root g,componentGenus g hg R r

 theorem componentGenus_hasGenus (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (r : Root g)
    [Nonempty (ComponentEdge g r.val.val)] :
    (componentRows g hg r.val.val R).HasGenus (componentGenus g hg R r) := by
  have hn : ¬IsEmpty (ComponentEdge g r.val.val) := not_isEmpty_of_nonempty _
  rw [componentGenus,if_neg hn]
  exact SurfaceRotationGenus.hasGenus _ (Classical.choice inferInstance,true)
    (componentGraph_connected g hg r.val r.property)

 theorem component_capped_euler (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (r : Root g) :
    Nat.card (ComponentVertex g r.val.val)+count (componentFace g hg r.val.val R)+
      (if IsEmpty (ComponentEdge g r.val.val) then 1 else 0)+2*componentGenus g hg R r=
      Nat.card (ComponentEdge g r.val.val)+2 := by
  by_cases he:IsEmpty (ComponentEdge g r.val.val)
  · letI:=he
    have hv:=component_isolated_card g hg r.val r.property
    rw [Nat.card_eq_fintype_card] at hv
    simp [componentGenus,he,hv]
  · letI : Nonempty (ComponentEdge g r.val.val):=not_isEmpty_iff.mp he
    have hh:=componentGenus_hasGenus g hg R r
    unfold RotationRows.HasGenus at hh
    simpa only [if_neg he,add_zero,Nat.card_eq_fintype_card,count,RotationRows.Face,
      componentFace,RotationRows.facePerm] using hh

 theorem isolated_iff_degree_zero (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) :
    (∀a:Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1≠v) ↔
      (g.toMultiGraph hg).selectedDegree Finset.univ v=0 := by
  rw [(g.toMultiGraph hg).degree_zero_iff_no_endpoints]
  constructor
  · intro h e
    exact ⟨h (e,true),h (e,false)⟩
  · intro h a
    rcases a with ⟨e,b⟩
    cases b
    · exact (h e).2
    · exact (h e).1

 theorem isolated_count (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    Fintype.card (Isolated (G:=g.toMultiGraph hg))=
      ∑r:Root g,if IsEmpty (ComponentEdge g r.val.val) then 1 else 0 := by
  rw [←isolated_card_eq_sum_roots g hg]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (isolated_iff_degree_zero g hg))

 theorem global_capped_euler (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) :
    g.vertices+Fintype.card (Boundary R)+2*totalGenus g hg R=
      g.edges.length+2*(g.toMultiGraph hg).componentCount Finset.univ := by
  unfold totalGenus
  have hs:=Finset.sum_congr rfl (fun r (_:r∈(Finset.univ:Finset (Root g)))=>component_capped_euler g hg R r)
  simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,smul_eq_mul] at hs
  have hv:=vertices_eq_sum_components g
  have he:=edges_eq_sum_components g hg
  have hf:=face_count_eq_sum_components g hg R
  have hi:=isolated_count g hg
  have hc:=componentCount_eq_roots g hg
  have hb : Fintype.card (Boundary R)=count (globalRowFace g hg R)+
      Fintype.card (Isolated (G:=g.toMultiGraph hg)) := by
    rw [Fintype.card_sum]
    congr 1
    exact Nat.card_eq_fintype_card.symm
  rw [←Finset.mul_sum] at hs
  omega


end PlanarHom.SurfaceRawEmbedding

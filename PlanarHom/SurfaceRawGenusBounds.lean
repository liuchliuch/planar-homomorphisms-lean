import PlanarHom.SurfaceRawComponentGenera
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRawEmbedding
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles SurfaceRibbonComplement
 private theorem genus_budget_arithmetic (v e b c t h a:ℕ)
    (he:v+b+2*h=e+2*c) (hb:e+2*c+2*t≤v+b+2*a) : h+t≤a := by omega

 theorem total_component_genus_bound (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (D : Data R) {ambient : ℕ} (hd:D.Valid ambient) :
    totalGenus g hg R+(∑j,D.regionGenus j)≤ambient := by
  have he:=global_capped_euler g hg R
  have hb:=D.ribbon_deficit_bound hd
  have hv : Fintype.card (Fin g.vertices)=g.vertices := Fintype.card_fin _
  have hec : Fintype.card (Fin g.edges.length)=g.edges.length := Fintype.card_fin _
  have hc : Fintype.card (Component (G:=g.toMultiGraph hg))=
      (g.toMultiGraph hg).componentCount Finset.univ := rfl
  rw [hv,hec,hc] at hb
  exact genus_budget_arithmetic _ _ _ _ _ (totalGenus g hg R) _ he hb

 theorem component_genus_le (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (D : Data R) {ambient : ℕ} (hd:D.Valid ambient)
    (r : Root g) : componentGenus g hg R r≤ambient := by
  have ht:=total_component_genus_bound g hg R D hd
  have hs:=Finset.single_le_sum (fun s (_:s∈(Finset.univ:Finset (Root g)))=>
    Nat.zero_le (componentGenus g hg R s)) (Finset.mem_univ r)
  change componentGenus g hg R r≤totalGenus g hg R at hs
  omega

 theorem nonempty_component_genus (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (D : Data R) {ambient : ℕ} (hd:D.Valid ambient)
    (r : Root g) [Nonempty (ComponentEdge g r.val.val)] :
    ∃h≤ambient,(componentRows g hg r.val.val R).HasGenus h :=
  ⟨componentGenus g hg R r,component_genus_le g hg R D hd r,componentGenus_hasGenus g hg R r⟩

end PlanarHom.SurfaceRawEmbedding

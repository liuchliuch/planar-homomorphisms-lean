import PlanarHom.PlanarityLRPlanarEuler
import PlanarHom.PlanarityLRComponentConnected
import PlanarHom.FinitePermutationFiberCount
import PlanarHom.FinitePermutationCycleTransport

/-! Actual DFS roots are exactly the ordinary occurrence graph components;
vertex and occurrence counts decompose over those computed roots. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

 abbrev Root (g : MixedCode) := {r : Fin g.vertices // height g r.val=0}

 def vertexRoot (g : MixedCode) (v : Fin g.vertices) : Root g :=
  ⟨⟨componentRoot g v.val,(componentRoot_spec g v.isLt).1⟩,(componentRoot_spec g v.isLt).2.2⟩

 def edgeRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) : Root g :=
  vertexRoot g ⟨source g e.val,(source_target_valid g hg e.isLt).1⟩

 @[simp] theorem vertexRoot_val (g : MixedCode) (v : Fin g.vertices) : (vertexRoot g v).val.val=componentRoot g v.val := rfl
 @[simp] theorem edgeRoot_val (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) :
    (edgeRoot g hg e).val.val=componentRoot g (source g e.val) := rfl

 theorem vertexRoot_eq_root (g : MixedCode) (r : Root g) : vertexRoot g r.val=r := by
  apply Subtype.ext
  exact Fin.ext (componentRoot_eq_self g r.val.isLt r.property)

 theorem root_eq_iff (g : MixedCode) (a b : Root g) : a=b ↔ a.val.val=b.val.val := by
  constructor
  · intro h; rw [h]
  · intro h; exact Subtype.ext (Fin.ext h)

 theorem vertexRoot_endpoints (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) :
    vertexRoot g ((g.toMultiGraph hg).src e)=vertexRoot g ((g.toMultiGraph hg).dst e) := by
  apply (root_eq_iff g _ _).mpr
  exact (original_host_componentRoot g hg (e,true)).trans (original_host_componentRoot g hg (e,false)).symm

 theorem componentGraph_lift_connected (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) {a b : ComponentVertex g r}
    (h : (componentGraph g hg r).componentSetoid Finset.univ a b) :
    (g.toMultiGraph hg).componentSetoid Finset.univ a.val b.val := by
  induction h with
  | rel a b h =>
    obtain ⟨e,_,rfl,rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨e.val,Finset.mem_univ _,rfl,rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

 theorem component_iff_vertexRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a b : Fin g.vertices) :
    (g.toMultiGraph hg).componentSetoid Finset.univ a b ↔ vertexRoot g a=vertexRoot g b := by
  constructor
  · exact (g.toMultiGraph hg).edgeConstant_respects Finset.univ (vertexRoot g)
      (fun e _ => vertexRoot_endpoints g hg e)
  · intro h
    let r := vertexRoot g a
    have hb : componentRoot g b.val=r.val.val := (congrArg (fun r : Root g => r.val.val) h).symm
    exact componentGraph_lift_connected g hg r.val.val
      (componentGraph_connected g hg r.val r.property ⟨a,rfl⟩ ⟨b,hb⟩)

 def rootComponentEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (g.toMultiGraph hg).Components Finset.univ ≃ Root g where
  toFun := Quotient.lift (vertexRoot g) (fun a b h => (component_iff_vertexRoot g hg a b).mp h)
  invFun r := Quotient.mk _ r.val
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      apply (component_iff_vertexRoot g hg _ _).mpr
      exact vertexRoot_eq_root g (vertexRoot g v)
  right_inv r := vertexRoot_eq_root g r

 theorem componentCount_eq_roots (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (g.toMultiGraph hg).componentCount Finset.univ=Fintype.card (Root g) :=
  Fintype.card_congr (rootComponentEquiv g hg)

 def componentVertexSigmaEquiv (g : MixedCode) : (Σr : Root g,ComponentVertex g r.val.val) ≃ Fin g.vertices :=
  Equiv.ofBijective (fun p => p.2.val) (by
    constructor
    · rintro ⟨r,a⟩ ⟨s,b⟩ h
      have hrs : r=s := (root_eq_iff g r s).mpr (a.property.symm.trans ((congrArg (fun v : Fin g.vertices => componentRoot g v.val) h).trans b.property))
      subst s
      exact congrArg (Sigma.mk r) (Subtype.ext h)
    · intro v
      exact ⟨⟨vertexRoot g v,⟨v,rfl⟩⟩,rfl⟩)

 def componentEdgeSigmaEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (Σr : Root g,ComponentEdge g r.val.val) ≃ Fin g.edges.length :=
  Equiv.ofBijective (fun p => p.2.val) (by
    constructor
    · rintro ⟨r,a⟩ ⟨s,b⟩ h
      have hrs : r=s := (root_eq_iff g r s).mpr (a.property.symm.trans ((congrArg (fun e : Fin g.edges.length => componentRoot g (source g e.val)) h).trans b.property))
      subst s
      exact congrArg (Sigma.mk r) (Subtype.ext h)
    · intro e
      exact ⟨⟨edgeRoot g hg e,⟨e,rfl⟩⟩,rfl⟩)

 theorem vertices_eq_sum_components (g : MixedCode) :
    g.vertices=∑r : Root g,Nat.card (ComponentVertex g r.val.val) := by
  have h := Fintype.card_congr (componentVertexSigmaEquiv g)
  simpa only [Fintype.card_sigma,Fintype.card_fin,Nat.card_eq_fintype_card] using h.symm

 theorem edges_eq_sum_components (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    g.edges.length=∑r : Root g,Nat.card (ComponentEdge g r.val.val) := by
  have h := Fintype.card_congr (componentEdgeSigmaEquiv g hg)
  simpa only [Fintype.card_sigma,Fintype.card_fin,Nat.card_eq_fintype_card] using h.symm
end PlanarHom.PlanarityLRRealization

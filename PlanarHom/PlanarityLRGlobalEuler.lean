import PlanarHom.PlanarityLRGlobalComponents

/-! Aggregate the actual per-component computed Euler identities. The explicit
nonempty-edge condition retains the distinction between isolates and faces. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityDepthFirstSearch FinitePermutationCycles

 def globalRowFace (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) : Equiv.Perm (Dart (Fin g.edges.length)) :=
  (reversePerm (Fin g.edges.length)).trans rows.rotation

 def faceRootLabel (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) : Root g := edgeRoot g hg a.1

 theorem faceRootLabel_preserved (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    faceRootLabel g hg (globalRowFace g hg rows a)=faceRootLabel g hg a := by
  apply (root_eq_iff g _ _).mpr
  change componentRoot g (PlanarityLRRawConstraints.source g (rows.rotation (reversePerm _ a)).1.val)=
    componentRoot g (PlanarityLRRawConstraints.source g a.1.val)
  rw [← original_host_componentRoot g hg (rows.rotation (reversePerm _ a)),rows.rotation_host,
    original_host_componentRoot]
  rfl

 def faceRootFiberEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : Root g) :
    Dart (ComponentEdge g r.val.val) ≃ {a : Dart (Fin g.edges.length) // faceRootLabel g hg a=r} where
  toFun a := ⟨componentDartLift g r.val.val a,(root_eq_iff g _ _).mpr a.1.property⟩
  invFun a := (⟨a.val.1,(root_eq_iff g _ _).mp a.property⟩,a.val.2)
  left_inv a := rfl
  right_inv a := rfl

 theorem componentFace_count_fiber (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (r : Root g) :
    count (componentFace g hg r.val.val rows)=count (fiberPermutation (globalRowFace g hg rows)
      (faceRootLabel g hg) (faceRootLabel_preserved g hg rows) r) := by
  apply count_of_step _ _ (faceRootFiberEquiv g hg r)
  intro a
  apply Subtype.ext
  exact componentFace_lift g hg r.val.val rows a

 theorem face_count_eq_sum_components (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) :
    count (globalRowFace g hg rows)=∑r : Root g,count (componentFace g hg r.val.val rows) := by
  rw [count_eq_sum_fibers _ (faceRootLabel g hg) (faceRootLabel_preserved g hg rows)]
  exact Finset.sum_congr rfl (fun r _ => (componentFace_count_fiber g hg rows r).symm)

 theorem planar_global_euler (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut)
    (hnoisolates : ∀r : Root g,Nonempty (ComponentEdge g r.val.val)) :
    g.vertices+count (globalRowFace g hp.1 (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2))=
      g.edges.length+2*(g.toMultiGraph hp.1).componentCount Finset.univ := by
  have hh : ∀r : Root g,Nat.card (ComponentVertex g r.val.val)+
      count (componentFace g hp.1 r.val.val (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2))=
        Nat.card (ComponentEdge g r.val.val)+2 := by
    intro r
    letI := hnoisolates r
    exact planar_computed_component_euler g hp r.val r.property
  have hs := Finset.sum_congr rfl (fun r (_ : r∈(Finset.univ : Finset (Root g))) => hh r)
  have hv := vertices_eq_sum_components g
  have he := edges_eq_sum_components g hp.1
  have hc := componentCount_eq_roots g hp.1
  have hf := face_count_eq_sum_components g hp.1
    (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  omega
end PlanarHom.PlanarityLRRealization

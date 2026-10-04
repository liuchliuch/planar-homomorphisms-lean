import PlanarHom.PlanarityLRComponentFaceWords

/-! NEW exact identification of the runtime's one omitted face in each actual
component. This is a combinatorial cycle choice, without an exterior oracle. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect
open PlanarityFaceCode

 theorem sameCycle_of_representative_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length))
    (he : representative g bits (eraseDart a)=representative g bits (eraseDart b)) :
    (facePermutation g hg bits).SameCycle a b := by
  let q := liftDart (representative g bits (eraseDart a)) (representative_valid g hg bits a)
  have ha : (facePermutation g hg bits).SameCycle a q := by
    apply (mem_orbit_iff_sameCycle g hg bits a q).mp
    simpa only [q,erase_liftDart] using representative_mem_orbit g hg bits a
  have hb : (facePermutation g hg bits).SameCycle b q := by
    apply (mem_orbit_iff_sameCycle g hg bits b q).mp
    simp only [q,erase_liftDart,he]
    exact representative_mem_orbit g hg bits b
  exact ha.trans hb.symm

 def rawSelectedRoot (g : MixedCode) (bits : List Bool) (a : Dart (Fin g.edges.length)) : PlanarityRotationCode.Dart :=
  rootRepresentative g bits (representative g bits (eraseDart a))

 theorem rawSelectedRoot_mem (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) : rawSelectedRoot g bits a∈representatives g bits :=
  rootRepresentative_mem g bits (representative_mem_representatives g hg bits a)

 theorem rawSelectedRoot_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) : (rawSelectedRoot g bits a).1<g.edges.length :=
  representative_index_of_mem g bits (rawSelectedRoot_mem g hg bits a)

 theorem rawSelectedRoot_component (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (rawSelectedRoot g bits a))=
      componentRoot g (dartHost g a) :=
  (rootRepresentative_component g bits (representative_mem_representatives g hg bits a)).trans
    (representative_componentRoot g hg bits a)

 def componentFaceRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) (r : ℕ)
    (base : Dart (ComponentEdge g r)) : Dart (ComponentEdge g r) :=
  (componentDartEquiv g hg r).symm
    ⟨liftDart (rawSelectedRoot g bits (componentDartLift g r base))
      (rawSelectedRoot_valid g hg bits (componentDartLift g r base)), by
        change componentRoot g (PlanarityRotationCode.host g (eraseDart (liftDart _ _)))=r
        rw [erase_liftDart]
        exact (rawSelectedRoot_component g hg bits _).trans (componentDartEquiv g hg r base).property⟩

@[simp] theorem componentFaceRoot_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base : Dart (ComponentEdge g r)) :
    eraseDart (componentDartLift g r (componentFaceRoot g hg bits r base))=
      rawSelectedRoot g bits (componentDartLift g r base) := rfl

 theorem component_nonroot_faceId_bounded (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base a : Dart (ComponentEdge g r))
    (hne : ¬(componentFace g hg r (directRotationRows g hg bits)).SameCycle a
      (componentFaceRoot g hg bits r base)) :
    faceId g bits (eraseDart (componentDartLift g r a))∈boundedFaces g bits := by
  let raw := componentDartLift g r a
  let rawbase := componentDartLift g r base
  have hmem := representative_mem_representatives g hg bits raw
  apply (mem_boundedFaces_iff g bits _).mpr
  refine ⟨representative g bits (eraseDart raw),hmem,?_,?_⟩
  · intro hfix
    have hrootEq : rootRepresentative g bits (representative g bits (eraseDart raw))=
        rawSelectedRoot g bits rawbase := by
      apply rootRepresentative_eq_of_component g bits hmem
      exact (representative_componentRoot g hg bits raw).trans
        ((componentDartEquiv g hg r a).property.trans
          ((componentDartEquiv g hg r base).property.symm.trans
            (representative_componentRoot g hg bits rawbase).symm))
    have hrep : representative g bits (eraseDart raw)=rawSelectedRoot g bits rawbase := hfix.symm.trans hrootEq
    apply hne
    apply (componentFace_sameCycle_iff g hg r (directRotationRows g hg bits) a _).mpr
    apply sameCycle_of_representative_eq g hg bits
    rw [componentFaceRoot_raw,representative_fixed_of_mem g bits (rawSelectedRoot_mem g hg bits rawbase)]
    exact hrep
  · simp only [faceId,representative_idempotent g hg bits raw]
    rfl

end PlanarHom.PlanarityLRRealization

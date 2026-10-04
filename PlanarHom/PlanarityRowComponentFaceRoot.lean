import PlanarHom.PlanarityRowComponentFaceWords
import PlanarHom.PlanarityRowFaceComponents

/-! NEW exact identification of the runtime's one omitted face in each actual
component. This is a combinatorial cycle choice, without an exterior oracle. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect
open PlanarityLRRealization

 theorem sameCycle_of_representative_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a b : Dart (Fin g.edges.length))
    (he : representative g rows (eraseDart a)=representative g rows (eraseDart b)) :
    (R.facePerm).SameCycle a b := by
  let q := liftDart (representative g rows (eraseDart a)) (representative_valid g hg rows R hrows a)
  have ha : (R.facePerm).SameCycle a q := by
    apply (mem_orbit_iff_sameCycle g hg rows R hrows a q).mp
    simpa only [q,erase_liftDart] using representative_mem_orbit g hg rows R hrows a
  have hb : (R.facePerm).SameCycle b q := by
    apply (mem_orbit_iff_sameCycle g hg rows R hrows b q).mp
    simp only [q,erase_liftDart,he]
    exact representative_mem_orbit g hg rows R hrows b
  exact ha.trans hb.symm

 def rawSelectedRoot (g : MixedCode) (rows : Rows) (a : Dart (Fin g.edges.length)) : PlanarityRotationCode.Dart :=
  rootRepresentative g rows (representative g rows (eraseDart a))

 theorem rawSelectedRoot_mem (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) : rawSelectedRoot g rows a∈representatives g rows :=
  rootRepresentative_mem g rows (representative_mem_representatives g hg rows R hrows a)

 theorem rawSelectedRoot_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) : (rawSelectedRoot g rows a).1<g.edges.length :=
  representative_index_of_mem g rows (rawSelectedRoot_mem g hg rows R hrows a)

 theorem rawSelectedRoot_component (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (rawSelectedRoot g rows a))=
      componentRoot g (dartHost g a) :=
  (rootRepresentative_component g rows (representative_mem_representatives g hg rows R hrows a)).trans
    (representative_componentRoot g hg rows R hrows a)

 def componentFaceRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ)
    (base : Dart (ComponentEdge g r)) : Dart (ComponentEdge g r) :=
  (componentDartEquiv g hg r).symm
    ⟨liftDart (rawSelectedRoot g rows (componentDartLift g r base))
      (rawSelectedRoot_valid g hg rows R hrows (componentDartLift g r base)), by
        change componentRoot g (PlanarityRotationCode.host g (eraseDart (liftDart _ _)))=r
        rw [erase_liftDart]
        exact (rawSelectedRoot_component g hg rows R hrows _).trans (componentDartEquiv g hg r base).property⟩

@[simp] theorem componentFaceRoot_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ) (base : Dart (ComponentEdge g r)) :
    eraseDart (componentDartLift g r (componentFaceRoot g hg rows R hrows r base))=
      rawSelectedRoot g rows (componentDartLift g r base) := rfl

 theorem component_nonroot_faceId_bounded (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ) (base a : Dart (ComponentEdge g r))
    (hne : ¬(componentFace g hg r (R)).SameCycle a
      (componentFaceRoot g hg rows R hrows r base)) :
    faceId g rows (eraseDart (componentDartLift g r a))∈boundedFaces g rows := by
  let raw := componentDartLift g r a
  let rawbase := componentDartLift g r base
  have hmem := representative_mem_representatives g hg rows R hrows raw
  apply (mem_boundedFaces_iff g rows _).mpr
  refine ⟨representative g rows (eraseDart raw),hmem,?_,?_⟩
  · intro hfix
    have hrootEq : rootRepresentative g rows (representative g rows (eraseDart raw))=
        rawSelectedRoot g rows rawbase := by
      apply rootRepresentative_eq_of_component g rows hmem
      exact (representative_componentRoot g hg rows R hrows raw).trans
        ((componentDartEquiv g hg r a).property.trans
          ((componentDartEquiv g hg r base).property.symm.trans
            (representative_componentRoot g hg rows R hrows rawbase).symm))
    have hrep : representative g rows (eraseDart raw)=rawSelectedRoot g rows rawbase := hfix.symm.trans hrootEq
    apply hne
    apply (componentFace_sameCycle_iff g hg r (R) a _).mpr
    apply sameCycle_of_representative_eq g hg rows R hrows
    rw [componentFaceRoot_raw,representative_fixed_of_mem g rows (rawSelectedRoot_mem g hg rows R hrows rawbase)]
    exact hrep
  · simp only [faceId,representative_idempotent g hg rows R hrows raw]
    rfl

end PlanarHom.PlanarityRowFaceCode

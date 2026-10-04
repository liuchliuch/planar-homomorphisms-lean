import PlanarHom.PlanarityRowFaceOrientationCorrectness
import PlanarHom.PlanarityLRComponentFaceWords

/-! NEW component cycle words for arbitrary realized numeric rows. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRRealization
open FinitePermutationCycles FinitePermutationReturnWords
 theorem componentFaceWord_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ)
    (a : Dart (ComponentEdge g r)) :
    (cycleWord (componentFace g hg r (R)) a).map
      (fun b => eraseDart (componentDartLift g r b))=
      boundary g rows (eraseDart (componentDartLift g r a)) := by
  rw [boundary_eq_period_walk g hg rows R hrows]
  simp only [cycleWord,orbitPrefix,List.map_map,Function.comp_def,componentFace_iterate_lift,componentFace_period]
  rfl

 theorem boundary_perm_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a b : Dart (Fin g.edges.length)) (h : (R.facePerm).SameCycle a b) :
    (boundary g rows (eraseDart a)).Perm (boundary g rows (eraseDart b)) := by
  rw [boundary_eq_period_walk g hg rows R hrows a,boundary_eq_period_walk g hg rows R hrows b]
  simpa only [cycleWord,orbitPrefix,List.map_map,Function.comp_def] using
    (cycleWord_perm_of_sameCycle (R.facePerm) a b h).map eraseDart

 theorem boundaryById_perm_componentFaceWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ) (a : Dart (ComponentEdge g r)) :
    (boundaryById g rows (faceId g rows (eraseDart (componentDartLift g r a)))).Perm
      ((cycleWord (componentFace g hg r (R)) a).map
        (fun b => eraseDart (componentDartLift g r b))) := by
  let raw := componentDartLift g r a
  let rep := liftDart (representative g rows (eraseDart raw)) (representative_valid g hg rows R hrows raw)
  have hc : (R.facePerm).SameCycle raw rep := by
    apply (mem_orbit_iff_sameCycle g hg rows R hrows raw rep).mp
    simpa only [rep,erase_liftDart] using representative_mem_orbit g hg rows R hrows raw
  rw [componentFaceWord_raw g hg rows R hrows,boundaryById_faceId g hg rows R hrows raw.1.isLt]
  simpa only [rep,erase_liftDart] using boundary_perm_sameCycle g hg rows R hrows rep raw hc.symm

end PlanarHom.PlanarityRowFaceCode

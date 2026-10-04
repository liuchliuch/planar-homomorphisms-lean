import PlanarHom.SurfaceRuntimeFaceRoots
import PlanarHom.PlanarityRowFaceOrientationCorrectness
import PlanarHom.FinitePermutationCycleWords

/-! NEW global face-product law for the actual row-table orientation program.
Every omitted root is identified by the proved full-graph root selector; no
connectedness or genus-zero assumption occurs. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization
open FinitePermutationCycles FinitePermutationReturnWords
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hr : Realizes g hg rows R)

include hr

theorem boundary_eq_cycleWord (a : Dart (Fin g.edges.length)) :
    boundary g rows (eraseDart a)=(cycleWord R.facePerm a).map eraseDart := by
  rw [boundary_eq_period_walk g hg rows R hr]
  simp only [cycleWord,orbitPrefix,List.map_map]
  rfl

theorem global_face_product_of_boundary (a : Dart (Fin g.edges.length)) (orientation : ℕ→Bool)
    (ho : FaceOdd orientation (boundary g rows (eraseDart a))) :
    (∏b : {b : Dart (Fin g.edges.length) // R.faceOf b=R.faceOf a},
      dartSign (fun e=>orientation e.val) b.val)=
      (-1:ℤ)^(Fintype.card {b : Dart (Fin g.edges.length) // R.faceOf b=R.faceOf a}+1) := by
  have hp : (∏b : {b : Dart (Fin g.edges.length) // R.faceOf b=R.faceOf a},
      dartSign (fun e=>orientation e.val) b.val)=
      boundarySign (fun e=>orientation e.val) (cycleWord R.facePerm a) := by
    convert cycleFiber_product R.facePerm a (dartSign (fun e=>orientation e.val)) using 1 <;>
      congr <;> exact Subsingleton.elim _ _
  have hc : Fintype.card {b : Dart (Fin g.edges.length) // R.faceOf b=R.faceOf a}=
      (cycleWord R.facePerm a).length := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (cycleFiberEquiv R.facePerm a)).symm
  rw [hp,hc]
  have hh:=ho.boundarySign
  rw [boundary_eq_cycleWord g hg rows R hr,List.length_map] at hh
  simpa only [boundarySign,List.map_map,Function.comp_def,dartSign,eraseDart] using hh

 theorem orientationLog_global_face_products :
    ∀q : R.Face,(runtimeFaceRoots g hg rows R hr).root q≠q→
      (∏a : {a : Dart (Fin g.edges.length) // R.faceOf a=q},
        dartSign (fun e=>logOrientation (orientationLog g rows) e.val) a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart (Fin g.edges.length) // R.faceOf a=q}+1) := by
  intro q hq
  let b:=faceRepresentative g hg rows R hr q
  have hb:b.val∈representatives g rows:=b.property
  have hne:rootRepresentative g rows b.val≠b.val:=by
    intro he
    exact hq ((runtimeFaceRoots_fixed_iff g hg rows R hr q).mpr he)
  have hi:faceId g rows b.val∈boundedFaces g rows:=
    (mem_boundedFaces_iff g rows _).mpr ⟨b.val,hb,hne,rfl⟩
  have ho:=orientationLog_faceOdd g hg rows R hr _ hi
  rw [boundaryById_faceId g hg rows R hr (representative_index_of_mem g rows hb),
    representative_fixed_of_mem g rows hb] at ho
  let a:=liftDart b.val (representative_index_of_mem g rows hb)
  have ha:R.faceOf a=q:=representativeFace_faceRepresentative g hg rows R hr q
  have hprod:=global_face_product_of_boundary g hg rows R hr a (logOrientation (orientationLog g rows))
    (by simpa only [a,erase_liftDart] using ho)
  exact ha ▸ hprod

end PlanarHom.PlanarityRowFaceCode

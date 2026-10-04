import PlanarHom.SurfaceFaceColumns
import PlanarHom.PlanarityRowFaceDualData

/-! NEW exact interpretation of emitted raw facial boundaries as the actual
columns of the F2 dual coboundary matrix. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization

 def boundaryVector (g : MixedCode) (ds : List PlanarityRotationCode.Dart) : Fin g.edges.length→ZMod 2 :=
  fun e=>if incidenceParity e.val ds then 1 else 0

 def fullTableVectors (g : MixedCode) (rows : Rows) : List (Fin g.edges.length→ZMod 2) :=
  (fullTable g rows).map (fun q=>boundaryVector g q.2)

 theorem fullTableVectors_eq (g : MixedCode) (rows : Rows) :
    fullTableVectors g rows=(representatives g rows).map (fun a=>boundaryVector g (boundary g rows a)) := by
  unfold fullTableVectors fullTable
  simp only [List.map_map,Function.comp_def]
  change ((representatives g rows).zipIdx.map ((fun a=>boundaryVector g (boundary g rows a)) ∘ Prod.fst))=_
  rw [←List.map_map,List.zipIdx_map_fst]

 theorem mem_boundary_iff_face (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a b : Dart (Fin g.edges.length)) :
    eraseDart b∈boundary g rows (eraseDart a) ↔ R.faceOf b=R.faceOf a := by
  rw [mem_boundary_iff_orbit g hg rows R hrows,mem_orbit_iff_sameCycle g hg rows R hrows]
  exact ⟨fun h=>Quotient.sound h.symm,fun h=>(Quotient.exact h).symm⟩

 theorem boundaryVector_eq_faceColumn (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a : Dart (Fin g.edges.length)) :
    boundaryVector g (boundary g rows (eraseDart a))=R.faceColumn (R.faceOf a) := by
  funext e
  rw [boundaryVector,incidenceParity_nodup e.val _ (boundary_nodup g hg rows R hrows a),R.faceColumn_apply]
  have ht:=mem_boundary_iff_face g hg rows R hrows a (e,true)
  have hf:=mem_boundary_iff_face g hg rows R hrows a (e,false)
  change (e.val,true)∈boundary g rows (eraseDart a) ↔ _ at ht
  change (e.val,false)∈boundary g rows (eraseDart a) ↔ _ at hf
  simp only [ht,hf]
  by_cases hx:R.faceOf (e,true)=R.faceOf a <;> by_cases hy:R.faceOf (e,false)=R.faceOf a <;>
    simp [hx,hy] <;> decide

 theorem fullTableVectors_range (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    {z | z∈fullTableVectors g rows}=Set.range R.faceColumn := by
  ext z
  rw [Set.mem_setOf_eq,fullTableVectors_eq,List.mem_map,Set.mem_range]
  constructor
  · rintro ⟨a,ha,rfl⟩
    let a':=liftDart a (representative_index_of_mem g rows ha)
    refine ⟨R.faceOf a',?_⟩
    simpa only [a',erase_liftDart] using (boundaryVector_eq_faceColumn g hg rows R hrows a').symm
  · rintro ⟨q,rfl⟩
    induction q using Quotient.inductionOn with
    | h a =>
      let b:=representative g rows (eraseDart a)
      have hb:b∈representatives g rows:=representative_mem_representatives g hg rows R hrows a
      let b':=liftDart b (representative_index_of_mem g rows hb)
      have hs:R.facePerm.SameCycle a b':=
        (mem_orbit_iff_sameCycle g hg rows R hrows a b').mp (by
          simpa only [b',b,erase_liftDart] using representative_mem_orbit g hg rows R hrows a)
      refine ⟨b,hb,?_⟩
      have hh:=boundaryVector_eq_faceColumn g hg rows R hrows b'
      simp only [b',erase_liftDart] at hh
      exact hh.trans (congrArg R.faceColumn (Quotient.sound hs.symm))

 theorem span_fullTableVectors (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    Submodule.span (ZMod 2) {z | z∈fullTableVectors g rows}=R.faceBoundarySpace := by
  rw [fullTableVectors_range g hg rows R hrows,←R.faceBoundarySpace_eq_span_columns]

end PlanarHom.PlanarityRowFaceCode

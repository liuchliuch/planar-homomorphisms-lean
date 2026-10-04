import PlanarHom.SurfaceRowFaceVectors
import PlanarHom.SurfaceRawHomologyRows
import PlanarHom.SurfaceBooleanRowSpanOn

/-! NEW exact span of the actual executable fullTable face rows. Invalid raw
inputs retain the total program definition; semantics uses only Valid and the
literal row realization, with no genus or orientation premise. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRawHomology
open SurfaceBooleanRows Complexity PlanarityLRRealization

theorem faceRow_eq_range (g : MixedCode) (ds : List (MultiGraph.Kasteleyn.Dart ℕ)) :
    faceRow g ds=(List.range g.edges.length).map (fun e=>MultiGraph.Kasteleyn.incidenceParity e ds) := by
  unfold faceRow
  change (g.edges.zipIdx.map ((fun e=>MultiGraph.Kasteleyn.incidenceParity e ds) ∘ Prod.snd))=_
  rw [←List.map_map,List.zipIdx_map_snd,←List.range_eq_range']

theorem finiteValue_faceRow (g : MixedCode) (ds : List (MultiGraph.Kasteleyn.Dart ℕ)) :
    finiteValue g.edges.length (faceRow g ds)=PlanarityRowFaceCode.boundaryVector g ds := by
  funext e
  rw [faceRow_eq_range]
  simp [finiteValue,value,bitValue,bitAt,PlanarityRowFaceCode.boundaryVector,List.getElem?_map,e.isLt]

theorem faceRows_span (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
    (hrows : PlanarityRowFaceCode.Realizes g hg rows R) :
    rowSpanOn g.edges.length (faceRows g rows)=R.faceBoundarySpace := by
  rw [rowSpanOn,←PlanarityRowFaceCode.span_fullTableVectors g hg rows R hrows]
  apply congrArg (Submodule.span (ZMod 2))
  ext z
  simp only [Set.mem_setOf_eq,faceRows,PlanarityRowFaceCode.fullTableVectors,List.mem_map]
  constructor
  · rintro ⟨r,⟨q,hq,rfl⟩,hr⟩
    exact ⟨q,hq,(finiteValue_faceRow g q.2).symm.trans hr⟩
  · rintro ⟨q,hq,hz⟩
    exact ⟨faceRow g q.2,⟨q,hq,rfl⟩,(finiteValue_faceRow g q.2).trans hz⟩

end PlanarHom.SurfaceRawHomology

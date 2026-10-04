import PlanarHom.SurfaceExtractComponentEquiv
import PlanarHom.SurfaceComponentCode
import PlanarHom.FisherCubicOrdering

/-! NEW literal supplied-row transport through stable component extraction.
The edge registry contains occurrence indices, so parallel edges stay distinct. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceComponentCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PlanarityLRDirect
open GraphComponentCode
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hr:PlanarityRowFaceCode.Realizes g hg rows R)

theorem edgeIds_eq_positions (xs:List ℕ) :
    edgeIds g xs=(FilteredOccurrence.positions g.edges (edgeInside xs)).map Fin.val := by
  rw [edgeIds,FisherCubicCode.zipIdx_eq,List.filter_map,List.map_map]
  rfl

theorem edgeIds_nodup (xs:List ℕ) : (edgeIds g xs).Nodup := by
  rw [edgeIds_eq_positions]
  exact (FilteredOccurrence.positions_nodup _ _).map Fin.val_injective

theorem edgeIds_length (xs:List ℕ) : (edgeIds g xs).length=(GraphComponentCode.extract g xs).edges.length := by
  rw [edgeIds_eq_positions,List.length_map,FilteredOccurrence.length_positions,extract_edges_length]

theorem edgeIds_get (xs:List ℕ) (e:Fin (GraphComponentCode.extract g xs).edges.length) :
    (edgeIds g xs).get (Fin.cast (edgeIds_length g xs).symm e)=(extractEdgeEmbedding g xs e).val := by
  simp only [List.get_eq_getElem,Fin.coe_cast,edgeIds_eq_positions,List.getElem_map]
  rfl

theorem edgeIds_idxOf_embedding (xs:List ℕ) (e:Fin (GraphComponentCode.extract g xs).edges.length) :
    (edgeIds g xs).idxOf (extractEdgeEmbedding g xs e).val=e.val := by
  rw [←edgeIds_get]
  exact List.get_idxOf (edgeIds_nodup g xs) _

def typedRows (xs:List ℕ) (hx:xs∈parts g) :
    RotationRows ((GraphComponentCode.extract g xs).toMultiGraph (extract_valid g hg xs)) :=
  (extractIncidenceEquiv g hg xs hx).symm.dartRelabel.rows
    (componentRows g hg (partRoot g xs hx).val.val R)

theorem typedRows_lift (xs:List ℕ) (hx:xs∈parts g) (v:Fin xs.length) :
    ((typedRows g hg R xs hx).row v).map
      (fun a=>(extractEdgeEmbedding g xs a.1,a.2))=
      R.row (extractVertexEmbedding g xs (part_nodup g xs hx) (part_vertex_lt g xs hx) v) := by
  let i:=extractIncidenceEquiv g hg xs hx
  change ((componentRow g hg (partRoot g xs hx).val.val R (i.vertex v)).map
    (fun a=>(i.edge.symm a.1,a.2))).map (fun a=>(extractEdgeEmbedding g xs a.1,a.2))=_
  rw [List.map_map]
  have he (a:Dart (ComponentEdge g (partRoot g xs hx).val.val)) :
      (extractEdgeEmbedding g xs (i.edge.symm a.1),a.2)=componentDartLift g (partRoot g xs hx).val.val a := by
    have h:=congrArg Subtype.val (i.edge.apply_symm_apply a.1)
    exact Prod.ext h rfl
  simp_rw [Function.comp_def,he]
  exact componentRow_lift g hg _ R _

include hr in
theorem extractRows_realizes (xs:List ℕ) (hx:xs∈parts g) :
    PlanarityRowFaceCode.Realizes (GraphComponentCode.extract g xs) (extract_valid g hg xs)
      (extractRows g rows xs) (typedRows g hg R xs hx) := by
  intro v
  have hv : v.val<xs.length:=v.isLt
  rw [extractRows,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hv,
    Option.map_some,Option.getD_some]
  let w:=extractVertexEmbedding g xs (part_nodup g xs hx) (part_vertex_lt g xs hx) v
  change (rows.getD w.val []).map _=_
  rw [hr w,←typedRows_lift g hg R xs hx v,List.map_map,List.map_map]
  apply List.map_congr_left
  intro a ha
  exact Prod.ext (edgeIds_idxOf_embedding g xs a.1) rfl

theorem typedRows_homology_finrank_le (xs:List ℕ) (hx:xs∈parts g) :
    Module.finrank (ZMod 2) (typedRows g hg R xs hx).Homology≤Module.finrank (ZMod 2) R.Homology := by
  rw [typedRows,(extractIncidenceEquiv g hg xs hx).symm.dartRelabel.homology_finrank]
  exact SurfaceRawEmbedding.component_homology_finrank_le g hg R (partRoot g xs hx)

end PlanarHom.SurfaceComponentCode

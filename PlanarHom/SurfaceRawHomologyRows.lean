import PlanarHom.SurfaceBooleanFiniteMachines
import PlanarHom.PlanarityRowFaceMachines

/-! NEW literal primal-incidence and full-face boundary matrices, computed
from the supplied occurrence graph and rotation rows. -/
namespace PlanarHom.SurfaceRawHomology
open SurfaceBooleanRows MultiGraph.Kasteleyn Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def shape (g : MixedCode) : Row := g.edges.map (fun _ => false)

def primalRows (g : MixedCode) : List Row :=
  (List.range g.vertices).map (fun v =>
    g.edges.map (fun e => decide (e.1=v) ^^ decide (e.2.1=v)))

def faceRow (g : MixedCode) (ds : List (MultiGraph.Kasteleyn.Dart ℕ)) : Row :=
  g.edges.zipIdx.map (fun p => incidenceParity p.2 ds)

def faceRows (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : List Row :=
  (PlanarityRowFaceCode.fullTable g rows).map (fun f => faceRow g f.2)

def cycleRows (g : MixedCode) : List Row := kernelRows (shape g) (primalRows g)

@[simp] theorem shape_length (g : MixedCode) : (shape g).length=g.edges.length := by simp [shape]
@[simp] theorem primalRows_length (g : MixedCode) : (primalRows g).length=g.vertices := by simp [primalRows]
@[simp] theorem faceRow_length (g : MixedCode) (ds) : (faceRow g ds).length=g.edges.length := by simp [faceRow]

theorem primalRows_width (g : MixedCode) (r : Row) (hr : r∈primalRows g) : r.length=g.edges.length := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
  simp

theorem faceRows_width (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) (r : Row)
    (hr : r∈faceRows g rows) : r.length=g.edges.length := by
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hr
  exact faceRow_length _ _

theorem fp_shape : FP MixedCode.encoding rowCode shape :=
  MixedCode.fp_edges.comp (ListMapMachines.fp_map GraphComponentMachines.edgeCode BitEncoding.bool
    (fun _ => false) (fp_const _ _ false))

theorem fp_primalRows : FP MixedCode.encoding rowCode.list primalRows := by
  let ec := GraphComponentMachines.edgeCode
  have hv := fp_fst BitEncoding.nat ec
  have he := fp_snd BitEncoding.nat ec
  have hs := he.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ht := (he.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb := (((hs.pair hv).comp PfaffianList.fp_nat_eq).pair
    ((ht.pair hv).comp PfaffianList.fp_nat_eq)).comp (fp_bool_gate (fun p => p.1 ^^ p.2))
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.nat ec BitEncoding.bool _ hb
  have hg := fp_fst MixedCode.encoding BitEncoding.nat
  have hi := fp_snd MixedCode.encoding BitEncoding.nat
  have hrow := (hi.pair (hg.comp MixedCode.fp_edges)).comp hm
  have hvs := MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_range
  exact ((fp_id MixedCode.encoding).pair hvs).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat rowCode _ hrow)

theorem fp_faceRow : FP (MixedCode.encoding.prod dartCode.list) rowCode
    (fun p => faceRow p.1 p.2) := by
  let ep := GraphComponentMachines.edgeCode.prod BitEncoding.nat
  have hds := fp_fst dartCode.list ep
  have hi := (fp_snd dartCode.list ep).comp (fp_snd GraphComponentMachines.edgeCode BitEncoding.nat)
  have hp := (hi.pair hds).comp fp_incidenceParity
  have hz := ((fp_fst MixedCode.encoding dartCode.list).comp MixedCode.fp_edges).comp
    (ListIndexMachines.fp_zipIdx GraphComponentMachines.edgeCode)
  exact ((fp_snd MixedCode.encoding dartCode.list).pair hz).comp
    (ListContextMachines.fp_mapWithContext dartCode.list ep BitEncoding.bool _ hp)

theorem fp_faceRows : FP PlanarityRowFaceCode.inputCode rowCode.list (fun p => faceRows p.1 p.2) := by
  have hg := fp_fst MixedCode.encoding faceCode
  have hds := (fp_snd MixedCode.encoding faceCode).comp (fp_snd BitEncoding.nat dartCode.list)
  have hrow := (hg.pair hds).comp fp_faceRow
  have hinput := fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode
  exact (hinput.pair PlanarityRowFaceCode.fp_fullTable).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding faceCode rowCode _ hrow)

theorem fp_cycleRows : FP MixedCode.encoding rowCode.list cycleRows :=
  (fp_shape.pair fp_primalRows).comp fp_kernelRows

end PlanarHom.SurfaceRawHomology

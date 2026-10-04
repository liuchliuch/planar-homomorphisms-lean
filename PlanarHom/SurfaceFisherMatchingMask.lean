import PlanarHom.FisherCubicWeightSemantics
import PlanarHom.SurfaceBooleanRowMachines

/-! NEW literal occurrence mask of the Fisher matching represented by a
source even-edge vector. Triangle completion is evaluated by three Boolean
port tests, including repeated endpoints of source loops. -/
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows FisherCodeMachines

def portBit (g : MixedCode) (bits : Row) (v j : ℕ) : Bool :=
  bitAt bits ((FisherCubicCode.row g v).getD j (0,false)).1

def triangleBit (g : MixedCode) (bits : Row) (v j : ℕ) : Bool :=
  !(portBit g bits v j) && portBit g bits v (FisherCubicCode.triangleSrc j) &&
    portBit g bits v (FisherCubicCode.triangleDst j)

def mask (g : MixedCode) (bits : Row) : Row :=
  (List.range g.edges.length).map (fun e => !(bitAt bits e)) ++
    (List.range g.vertices).flatMap (fun v => (List.range 3).map (triangleBit g bits v))

end PlanarHom.SurfaceFisherMatching

noncomputable section
open Classical
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows FisherCodeMachines MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)

def sourceSet (bits : Row) : Finset (Fin g.edges.length) :=
  Finset.univ.filter (fun e => bitAt bits e.val=true)

def typedMatching (bits : Row) : Finset (Fin g.edges.length ⊕ (Fin g.vertices×Fin 3)) :=
  decoratedEdges (sourceSet g bits)ᶜ
    (fun v => triangleCompletion (selectedPorts (FisherCubicCode.ports g hg hc) (sourceSet g bits)ᶜ v))

theorem triangleCompletion_mem (B : Finset (Fin 3)) (j : Fin 3) :
    j∈triangleCompletion B ↔ j∈B ∧ triangle.src j∉B ∧ triangle.dst j∉B := by
  revert B j
  decide +kernel

theorem portBit_eq (bits : Row) (v : Fin g.vertices) (j : Fin 3) :
    portBit g bits v.val j.val=bitAt bits ((FisherCubicCode.ports g hg hc) (v,j)).1.val := by
  rw [portBit,FisherCubicCode.row_get_ports g hg hc v j]
  rfl

theorem triangleBit_eq (bits : Row) (v : Fin g.vertices) (j : Fin 3) :
    triangleBit g bits v.val j.val=decide (Sum.inr (v,j)∈typedMatching g hg hc bits) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [triangleBit,Bool.and_eq_true,Bool.not_eq_true',typedMatching,decoratedEdges,
    Finset.mem_disjSum,internalEdges,Finset.mem_filter,Finset.mem_univ,true_and,triangleCompletion_mem,
    selectedPorts,Finset.mem_compl,sourceSet]
  rw [←FisherCubicCode.triangleSrc_eq j,←FisherCubicCode.triangleDst_eq j,
    portBit_eq g hg hc bits v j,portBit_eq g hg hc bits v (triangle.src j),
    portBit_eq g hg hc bits v (triangle.dst j)]
  simp [and_assoc]

theorem mask_eq_map (bits : Row) : mask g bits=(FisherCubicCode.edgeList g).map
    (fun e => decide (e∈typedMatching g hg hc bits)) := by
  unfold mask FisherCubicCode.edgeList
  rw [List.map_append,List.map_map,List.map_map]
  apply congrArg₂ List.append
  · rw [←List.map_coe_finRange g.edges.length,List.map_map]
    apply List.map_congr_left
    intro e he
    simp [typedMatching,decoratedEdges,sourceSet,Bool.not_eq_true]
  · simp only [FisherCubicCode.vertexList,SProd.sprod,List.product,List.map_flatMap,List.map_map]
    rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
    congr 1
    funext v
    rw [←List.map_coe_finRange 3,List.map_map]
    apply List.map_congr_left
    intro j hj
    exact triangleBit_eq g hg hc bits v j

theorem mask_get (bits : Row) (e : Fin g.edges.length ⊕ (Fin g.vertices×Fin 3)) :
    bitAt (mask g bits) ((FisherCubicCode.incidenceEquiv g hg hc).edge e).val=
      decide (e∈typedMatching g hg hc bits) := by
  rw [bitAt,←List.getD_eq_getElem?_getD,FisherCubicCode.incidenceEquiv_edge_val,mask_eq_map g hg hc]
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
    getD_map_idxOf (FisherCubicCode.edgeList g) (fun e => decide (e∈typedMatching g hg hc bits)) e
      (FisherCubicCode.edgeList_mem g e) false

theorem typedMatching_perfect (bits : Row) (heven : (g.toMultiGraph hg).EvenSubgraph (sourceSet g bits)) :
    (Fisher.cubicDecoration (FisherCubicCode.ports g hg hc)).PerfectMatching (typedMatching g hg hc bits) := by
  have hs : (Fisher.cubicOriginal (FisherCubicCode.ports g hg hc)).EvenSubgraph (sourceSet g bits) := by
    simpa only [FisherCubicCode.cubicOriginal_ports] using heven
  have hh := ((Fisher.cubicFisherEquiv (FisherCubicCode.ports g hg hc)) ⟨sourceSet g bits,hs⟩).property
  convert hh using 1
  ext e
  cases e <;> simp [typedMatching,Fisher.cubicFisherEquiv,decoratedEdges,internalEdges,selectedPorts]

end PlanarHom.SurfaceFisherMatching

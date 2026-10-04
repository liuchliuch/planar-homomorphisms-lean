import PlanarHom.ColoringIncidenceTransport
import PlanarHom.PottsRandomCluster

/-! NEW exact actual-component transport under the emitter's occurrence and
vertex bijections. No component-count assumption is needed for division. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.IncidenceEquiv
variable {V E W F : Type} [Fintype E] [Fintype F]
variable {G : MultiGraph V E} {H : MultiGraph W F} (i:IncidenceEquiv G H)

 theorem component_map {u v:V} (h:G.componentSetoid Finset.univ u v) :
    H.componentSetoid Finset.univ (i.vertex u) (i.vertex v) := by
  let color:V→H.Components Finset.univ:=fun v=>Quotient.mk _ (i.vertex v)
  have hc:G.EdgeConstant Finset.univ color:=by
    intro e _
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨i.edge e,Finset.mem_univ _,i.src_eq e,i.dst_eq e⟩)
  exact Quotient.exact (G.edgeConstant_respects Finset.univ color hc h)

 def components : G.Components Finset.univ ≃ H.Components Finset.univ where
  toFun:=Quotient.map i.vertex (fun _ _ h=>i.component_map h)
  invFun:=Quotient.map i.vertex.symm (fun _ _ h=>i.symm.component_map h)
  left_inv q:=Quotient.inductionOn q (fun v=>congrArg (Quotient.mk _) (i.vertex.symm_apply_apply v))
  right_inv q:=Quotient.inductionOn q (fun v=>congrArg (Quotient.mk _) (i.vertex.apply_symm_apply v))

include i in
 theorem componentCount_eq [Fintype V] [Fintype W] :
    H.componentCount Finset.univ=G.componentCount Finset.univ := (Fintype.card_congr i.components).symm

end PlanarHom.MultiGraph.IncidenceEquiv

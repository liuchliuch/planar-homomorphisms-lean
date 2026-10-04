import PlanarHom.FisherExpansionGlobalFaces
import PlanarHom.FisherComponentCounts

/-! NEW full disconnected Euler transfer, including isolated source vertices,
through the literal expansion and arbitrary-port triangle decoration. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.DartRelabel
open Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable {G : MultiGraph V E} {H : MultiGraph W F}
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]

 theorem euler_global (e : DartRelabel G H) (R : RotationRows G)
    (h : Fintype.card V+count R.facePerm=Fintype.card E+2*G.componentCount Finset.univ) :
    Fintype.card W+count (e.rows R).facePerm=Fintype.card F+2*H.componentCount Finset.univ := by
  rw [e.face_count,←e.edge_card,←Fintype.card_congr e.vertex,e.componentCount]
  exact h

end PlanarHom.MultiGraph.DartRelabel
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

 theorem expansion_euler_global (o : G.IncidenceOrdering)
    (h : Fintype.card V+count o.rotationRows.facePerm+Fintype.card (IsolatedVertex o)=
      Fintype.card E+2*G.componentCount Finset.univ) :
    Fintype.card (ExpansionVertex o)+count (expansionRows o).facePerm=
      Fintype.card (ExpansionEdge o)+2*(expansionGraph o).componentCount Finset.univ := by
  rw [expansion_vertexCount,expansion_edgeCount,expansion_face_count_global,expansion_componentCount]
  omega

 theorem polygon_euler_global [DecidableEq (Dart E)] (R : RotationRows G)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (h : Fintype.card V+count R.facePerm=Fintype.card E+2*G.componentCount Finset.univ) :
    Fintype.card (Dart E)+count (polygonRows R).facePerm=
      Fintype.card (E⊕Dart E)+2*(polygonGraph R).componentCount Finset.univ := by
  rw [polygon_face_count,rotation_count_of_incident R hinc,polygon_componentCount R hinc]
  simp only [Dart,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum]
  omega

 theorem cubicInherited_euler_global [DecidableEq (Dart E)]
    (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))
    (h : Fintype.card V+count R.facePerm=Fintype.card E+2*(cubicOriginal p).componentCount Finset.univ) :
    Fintype.card (V×Fin 3)+count (cubicInheritedRows p R).facePerm=
      Fintype.card (E⊕(V×Fin 3))+2*(cubicDecoration p).componentCount Finset.univ :=
  (cubicRelabel p R).euler_global (polygonRows R) (polygon_euler_global R (cubicOriginal_incident p) h)

end PlanarHom.Fisher

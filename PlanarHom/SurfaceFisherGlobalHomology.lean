import PlanarHom.SurfaceHomologyCountTransport
import PlanarHom.SurfaceFisherCodeSemantics
import PlanarHom.FisherInheritedEuler
import PlanarHom.OccurrenceIsolatedComponents

/-! NEW exact homology-dimension preservation for the whole serialized Fisher
pipeline. The proof keeps the original isolate correction and all connected
components; no connected-input or sphere-Euler premise occurs. -/
noncomputable section
open Classical
open Matrix Module
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open SurfaceRibbonComplement
variable {V E : Type} [Fintype V] [Fintype E] {G:MultiGraph V E}

 theorem incident_of_degree_pos (h:∀v,0<G.selectedDegree Finset.univ v) :
    ∀v,∃a:Dart E,(G.dartPair a).1=v := by
  intro v
  by_contra hn
  have hz:G.selectedDegree Finset.univ v=0 := by
    apply (G.degree_zero_iff_no_endpoints v).mpr
    intro e
    exact ⟨fun he=>hn ⟨(e,true),he⟩,fun he=>hn ⟨(e,false),he⟩⟩
  have hp:=h v
  omega

 theorem ordering_isolated_card (o:G.IncidenceOrdering) :
    Fintype.card (IsolatedVertex o)=Fintype.card (Isolated (G:=G)) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro v
  rw [o.degree_eq,G.degree_zero_iff_no_endpoints]
  constructor
  · intro h a
    rcases a with ⟨e,b⟩
    cases b
    · exact (h e).2
    · exact (h e).1
  · intro h e
    exact ⟨h (e,true),h (e,false)⟩

 theorem expansion_homology_finrank [DecidableEq (Dart E)] (R:RotationRows G) :
    finrank (ZMod 2) (expansionRows R.incidenceOrdering).Homology=finrank (ZMod 2) R.Homology := by
  let o:=R.incidenceOrdering
  have hS:=R.homology_finrank_count_euler
  have hT:=(expansionRows o).homology_finrank_incident
    (incident_of_degree_pos (fun v=>by rw [expansion_is_cubic o]; omega))
  rw [expansion_vertexCount,expansion_edgeCount,expansion_face_count_global,expansion_componentCount] at hT
  have hi:=ordering_isolated_card o
  rw [ordering_face_decidable o _ ‹DecidableEq (Dart E)›,incidenceOrdering_face R,hi] at hT
  change finrank (ZMod 2) (expansionRows o).Homology=finrank (ZMod 2) R.Homology
  omega

 theorem polygon_incident [DecidableEq (Dart E)] (R:RotationRows G) :
    ∀v:Dart E,∃a:Dart (E⊕Dart E),((polygonGraph R).dartPair a).1=v := by
  rintro ⟨e,b⟩
  refine ⟨(.inl e,b),?_⟩
  cases b <;> rfl

 theorem polygon_homology_finrank [DecidableEq (Dart E)] (R:RotationRows G)
    (hinc:∀v,∃a:Dart E,(G.dartPair a).1=v) :
    finrank (ZMod 2) (polygonRows R).Homology=finrank (ZMod 2) R.Homology := by
  have hS:=R.homology_finrank_incident hinc
  have hT:=(polygonRows R).homology_finrank_incident (polygon_incident R)
  rw [polygon_face_count,rotation_count_of_incident R hinc,polygon_componentCount R hinc] at hT
  simp only [Dart,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum] at hT
  omega

 theorem cubicInherited_homology_finrank [DecidableEq (Dart E)]
    (p:(V×Fin 3)≃(E×Bool)) (R:RotationRows (cubicOriginal p)) :
    finrank (ZMod 2) (cubicInheritedRows p R).Homology=finrank (ZMod 2) R.Homology := by
  rw [cubicInheritedRows,MultiGraph.DartRelabel.homology_finrank]
  exact polygon_homology_finrank R (cubicOriginal_incident p)

end PlanarHom.Fisher
namespace PlanarHom.SurfaceFisherCode
open Complexity MultiGraph MultiGraph.Kasteleyn Fisher PlanarityLRRealization SurfaceRibbonComplement
variable (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (rows:Rows)
variable (R:RotationRows (g.toMultiGraph hg)) (hr:PlanarityRowFaceCode.Realizes g hg rows R)

 theorem typedExpansionRows_homology_finrank :
    finrank (ZMod 2) (typedExpansionRows g hg rows R hr).Homology=finrank (ZMod 2) R.Homology := by
  unfold typedExpansionRows
  rw [FisherInheritedRowCode.typedExpansionRows_eq_redecidable,
    MultiGraph.DartRelabel.homology_finrank,RotationRows.redecidable_homology_finrank]
  exact expansion_homology_finrank R

 theorem typedRows_homology_finrank :
    finrank (ZMod 2) (typedRows g hg rows R hr).Homology=finrank (ZMod 2) R.Homology := by
  unfold typedRows FisherInheritedRowCode.typedCubicRows
  rw [MultiGraph.DartRelabel.homology_finrank,RotationRows.redecidable_homology_finrank,
    cubicInherited_homology_finrank]
  exact typedExpansionRows_homology_finrank g hg rows R hr

 theorem typedRows_homology_finrank_le (D:Data R) {ambient:ℕ} (hd:D.Valid ambient) :
    finrank (ZMod 2) (typedRows g hg rows R hr).Homology≤2*ambient := by
  rw [typedRows_homology_finrank]
  exact R.homology_finrank_le D hd

end PlanarHom.SurfaceFisherCode

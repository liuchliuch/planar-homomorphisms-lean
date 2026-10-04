import PlanarHom.FisherNumericEnumeration
import PlanarHom.FisherRotationOrdering

/-! NEW exact interpretation of the executable reversed LR rows as a complete
Fisher incidence ordering. This is incidence data, with no drawing premise. -/
noncomputable section
open Classical
namespace PlanarHom.FisherContourOrder
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)

 def ordering : (g.toMultiGraph hg).IncidenceOrdering :=
  (directRotationRows g hg (PlanarityLRConstraints.decideAligned g).2).incidenceOrdering

 def Realizes (rows : Rows) (o : (g.toMultiGraph hg).IncidenceOrdering) : Prop :=
  ∀v:Fin g.vertices,FisherExpansionCode.row rows v.val=
    (List.ofFn (fun i:Fin (o.degree v)=>o.darts ⟨v,i⟩)).map eraseDart

 theorem computed_realizes : Realizes g hg (computedRows g) (ordering g hg) := by
  intro v
  have hrow : FisherExpansionCode.row (computedRows g) v.val =
      (PlanarityLRDirect.directRow g (PlanarityLRConstraints.decideAligned g).2 v.val).map PlanarityRotationCode.reverse := by
    simp [FisherExpansionCode.row,computedRows,List.getD_eq_getElem?_getD,v.isLt]
  rw [hrow]
  change _ = (List.ofFn (fun i=>reversePerm _ ((typedDirectRow g hg (PlanarityLRConstraints.decideAligned g).2 v).get i))).map eraseDart
  rw [List.ofFn_comp',List.ofFn_get,List.map_map]
  rw [←erase_typedDirectRow g hg (PlanarityLRConstraints.decideAligned g).2 v,List.map_map]
  rfl

 theorem Realizes.degree_eq {rows : Rows} {o : (g.toMultiGraph hg).IncidenceOrdering}
    (hr : Realizes g hg rows o) (v : Fin g.vertices) :
    o.degree v=(FisherExpansionCode.row rows v.val).length := by
  rw [hr v]
  simp

end PlanarHom.FisherContourOrder

import PlanarHom.SurfaceFisherCodeProgram
import PlanarHom.FisherCubicRowSemantics
import PlanarHom.FisherPipelineValidity

/-! NEW literal supplied-row incidence, validity, and inherited-row semantics
for both executable Fisher stages. No planarity or genus premise is used. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceFisherCode
open Complexity MultiGraph Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hr : PlanarityRowFaceCode.Realizes g hg rows R)

theorem orderRows_get (v : ℕ) : (orderRows rows).getD v []=
    (rows.getD v []).map PlanarityRotationCode.reverse := by
  simp only [orderRows,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases hx:rows[v]? <;> simp [hx]

include hg R hr

theorem orderRows_realizes : FisherContourOrder.Realizes g hg (orderRows rows) R.incidenceOrdering := by
  intro v
  change (orderRows rows).getD v.val []=_
  rw [orderRows_get,hr v]
  change ((R.row v).map eraseDart).map PlanarityRotationCode.reverse=
    (List.ofFn (fun i=>reversePerm _ ((R.row v).get i))).map eraseDart
  rw [List.ofFn_comp',List.ofFn_get,List.map_map,List.map_map]
  rfl

theorem intermediate_valid : (intermediate g rows).Valid 1 0 :=
  FisherExpansionCode.valid g hg R.incidenceOrdering (orderRows_realizes g hg rows R hr)

def expansionIncidence : IncidenceEquiv (expansionGraph R.incidenceOrdering)
    ((intermediate g rows).toMultiGraph (intermediate_valid g hg rows R hr)) :=
  FisherExpansionCode.incidenceEquiv g hg R.incidenceOrdering (orderRows_realizes g hg rows R hr)

theorem intermediate_cubic : ∀v,((intermediate g rows).toMultiGraph (intermediate_valid g hg rows R hr)).selectedDegree Finset.univ v=3 := by
  intro v
  obtain ⟨q,rfl⟩:=(expansionIncidence g hg rows R hr).vertex.surjective v
  exact ((expansionIncidence g hg rows R hr).degree_univ q).trans (expansion_is_cubic _ q)

theorem valid : (code g rows).Valid 1 0 :=
  FisherCubicCode.valid (intermediate g rows) (intermediate_valid g hg rows R hr) (intermediate_cubic g hg rows R hr)

def typedExpansionRows : RotationRows ((intermediate g rows).toMultiGraph (intermediate_valid g hg rows R hr)) :=
  FisherInheritedRowCode.typedExpansionRows g hg R.incidenceOrdering (orderRows_realizes g hg rows R hr)

theorem expansionRows_realizes : PlanarityRowFaceCode.Realizes (intermediate g rows)
    (intermediate_valid g hg rows R hr) (expansionRows g rows) (typedExpansionRows g hg rows R hr) := by
  intro w
  simp only [expansionRows,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range w.isLt,
    Option.map_some,Option.getD_some]
  let i:=expansionIncidence g hg rows R hr
  obtain ⟨q,rfl⟩:=i.vertex.surjective w
  have hh:=FisherInheritedRowCode.expansionRow_eq g hg R.incidenceOrdering (orderRows_realizes g hg rows R hr) q
  change FisherInheritedRowCode.expansionRow g (orderRows rows) (i.vertex q).val=
    ((Fisher.expansionRow R.incidenceOrdering (i.vertex.symm (i.vertex q))).map
      (fun a=>(i.edge a.1,a.2))).map eraseDart
  rw [Equiv.symm_apply_apply,List.map_map]
  exact hh

def typedRows : RotationRows ((code g rows).toMultiGraph (valid g hg rows R hr)) :=
  FisherInheritedRowCode.typedCubicRows (intermediate g rows) (intermediate_valid g hg rows R hr)
    (intermediate_cubic g hg rows R hr) (typedExpansionRows g hg rows R hr)

theorem inheritedRows_realizes : PlanarityRowFaceCode.Realizes (code g rows)
    (valid g hg rows R hr) (inheritedRows g rows) (typedRows g hg rows R hr) :=
  FisherInheritedRowCode.cubicRows_realizes (intermediate g rows) (intermediate_valid g hg rows R hr)
    (intermediate_cubic g hg rows R hr) (expansionRows g rows) (typedExpansionRows g hg rows R hr)
    (expansionRows_realizes g hg rows R hr)

end PlanarHom.SurfaceFisherCode

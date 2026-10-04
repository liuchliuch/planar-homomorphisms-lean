import PlanarHom.PlanarityRowFaceLabels
import PlanarHom.OccurrenceKasteleynDual

/-! NEW literal two-sided dual incidence. Original occurrences keep their exact
face IDs; out-of-range numeric edges have equal sentinel endpoints and no parity. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization
open MultiGraph.Kasteleyn

 def dualData (g : MixedCode) (rows : Rows) : DualIncidence ℕ ℕ where
   left e := if e<g.edges.length then faceId g rows (e,true) else (representatives g rows).length
   right e := if e<g.edges.length then faceId g rows (e,false) else (representatives g rows).length

@[simp] theorem dualData_left (g : MixedCode) (rows : Rows) {e : ℕ} (he : e<g.edges.length) :
    (dualData g rows).left e=faceId g rows (e,true) := by simp [dualData,he]
@[simp] theorem dualData_right (g : MixedCode) (rows : Rows) {e : ℕ} (he : e<g.edges.length) :
    (dualData g rows).right e=faceId g rows (e,false) := by simp [dualData,he]

 theorem incidenceParity_nodup (e : ℕ) (ds : List PlanarityRotationCode.Dart) (hn : ds.Nodup) :
    incidenceParity e ds = (decide ((e,true)∈ds) ^^ decide ((e,false)∈ds)) := by
  induction ds with
  | nil => simp [incidenceParity]
  | cons a ds ih =>
    have hnot:= (List.nodup_cons.mp hn).1
    have ht:=ih (List.nodup_cons.mp hn).2
    rcases a with ⟨v,b⟩
    by_cases hv:v=e
    · subst v
      cases b <;> simp_all [incidenceParity]
    · simp [incidenceParity,hv,ht,Prod.mk.injEq,Ne.symm hv]

 theorem dualData_compatible (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) : (dualData g rows).Compatible (boundaryById g rows) := by
  intro e f
  rw [incidenceParity_nodup e _ (boundaryById_nodup g hg rows R hrows f)]
  by_cases he:e<g.edges.length
  · rw [dualData_left g rows he,dualData_right g rows he]
    simp only [mem_boundaryById_iff g hg rows R hrows (a := (e,true)) he f,
      mem_boundaryById_iff g hg rows R hrows (a := (e,false)) he f]
  · have ht:(e,true)∉boundaryById g rows f := fun h=>he (boundaryById_index_valid g hg rows R hrows f h)
    have hf:(e,false)∉boundaryById g rows f := fun h=>he (boundaryById_index_valid g hg rows R hrows f h)
    simp [dualData,he,ht,hf]

/-- Both opposite darts of a bridge can occupy one face; they cancel exactly. -/
 theorem sameFace_incidence_even (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) {e : ℕ} (he : e<g.edges.length)
    (hs : faceId g rows (e,true)=faceId g rows (e,false)) (f : ℕ) :
    incidenceParity e (boundaryById g rows f)=false := by
  rw [dualData_compatible g hg rows R hrows e f,dualData_left g rows he,dualData_right g rows he,hs]
  simp

end PlanarHom.PlanarityRowFaceCode

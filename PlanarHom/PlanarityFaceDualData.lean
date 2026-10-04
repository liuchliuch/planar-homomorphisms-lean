import PlanarHom.PlanarityFaceLabels
import PlanarHom.OccurrenceKasteleynDual

/-! NEW literal two-sided dual incidence. Original occurrences keep their exact
face IDs; out-of-range numeric edges have equal sentinel endpoints and no parity. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization
open MultiGraph.Kasteleyn

 def dualData (g : MixedCode) (bits : List Bool) : DualIncidence ℕ ℕ where
   left e := if e<g.edges.length then faceId g bits (e,true) else (representatives g bits).length
   right e := if e<g.edges.length then faceId g bits (e,false) else (representatives g bits).length

@[simp] theorem dualData_left (g : MixedCode) (bits : List Bool) {e : ℕ} (he : e<g.edges.length) :
    (dualData g bits).left e=faceId g bits (e,true) := by simp [dualData,he]
@[simp] theorem dualData_right (g : MixedCode) (bits : List Bool) {e : ℕ} (he : e<g.edges.length) :
    (dualData g bits).right e=faceId g bits (e,false) := by simp [dualData,he]

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
    (bits : List Bool) : (dualData g bits).Compatible (boundaryById g bits) := by
  intro e f
  rw [incidenceParity_nodup e _ (boundaryById_nodup g hg bits f)]
  by_cases he:e<g.edges.length
  · rw [dualData_left g bits he,dualData_right g bits he]
    simp only [mem_boundaryById_iff g hg bits (a := (e,true)) he f,
      mem_boundaryById_iff g hg bits (a := (e,false)) he f]
  · have ht:(e,true)∉boundaryById g bits f := fun h=>he (boundaryById_index_valid g hg bits f h)
    have hf:(e,false)∉boundaryById g bits f := fun h=>he (boundaryById_index_valid g hg bits f h)
    simp [dualData,he,ht,hf]

/-- Both opposite darts of a bridge can occupy one face; they cancel exactly. -/
 theorem sameFace_incidence_even (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : e<g.edges.length)
    (hs : faceId g bits (e,true)=faceId g bits (e,false)) (f : ℕ) :
    incidenceParity e (boundaryById g bits f)=false := by
  rw [dualData_compatible g hg bits e f,dualData_left g bits he,dualData_right g bits he,hs]
  simp

end PlanarHom.PlanarityFaceCode

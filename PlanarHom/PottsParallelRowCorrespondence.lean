import PlanarHom.UniformParallelCodeIncidence
import PlanarHom.PottsInheritedParallelRows
import PlanarHom.ParallelSourceRows

/-! NEW exact numeric correspondence for inherited parallel rows. The typed
source occurrence/copy pair is sent to the actual emitted index e*t+r, and
both endpoint directions retain the same opposite copy order as the runtime. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsParallelRowCorrespondence
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PottsSourceInverseRows
variable {m t : ℕ}

def eraseCopy (a : Dart (Fin m×Fin t)) : PlanarityRotationCode.Dart :=
  (a.1.1.val*t+a.1.2.val,a.2)

theorem copies_erase (a : Dart (Fin m)) :
    (ParallelSource.copies t a).map eraseCopy=
      parallelDartBlock t (a.1.val,a.2) := by
  rcases a with ⟨e,b⟩
  simp only [ParallelSource.copies,List.map_map,Function.comp_def,ParallelSource.copyDart,eraseCopy,
    parallelDartBlock,ParallelSource.orientedIndex]
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    change ((List.finRange t).map (fun i=>((e.val*t+i.rev.val),false)))=
      ((List.range t).reverse.map (fun i=>(e.val*t+i,false)))
    rw [show (fun i : Fin t=>(e.val*t+i.rev.val,false))=
      (fun i : Fin t=>(e.val*t+i.val,false)) ∘ Fin.rev from rfl]
    rw [←List.map_map,←List.finRange_reverse,List.map_reverse]
    rw [show (List.finRange t).map (fun i=>(e.val*t+i.val,false))=
      (List.range t).map (fun i=>(e.val*t+i,false)) by
        rw [←List.map_coe_finRange, List.map_map]; rfl]
    rw [List.map_reverse]
  · simp only [ite_true]
    change ((List.finRange t).map (fun i=>(e.val*t+i.val,true)))=
      ((List.range t).map (fun i=>(e.val*t+i,true)))
    rw [←List.map_coe_finRange,List.map_map]
    rfl

theorem expand_erase (xs : List (Dart (Fin m))) :
    (ParallelSource.expand t xs).map eraseCopy=
      parallelRow t (xs.map (fun a=>(a.1.val,a.2))) := by
  simp only [ParallelSource.expand,List.map_flatMap,copies_erase,parallelRow,List.flatMap_map]

@[simp] theorem incidence_erase (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ)
    (a : Dart (Fin g.edges.length×Fin t)) :
    eraseDart ((UniformParallelCode.incidence g hg t).dartRelabel.dart a)=eraseCopy a := by
  rcases a with ⟨⟨e,r⟩,b⟩
  apply Prod.ext
  · exact UniformParallelCode.edgeEquiv_val g hg t e r
  · rfl

def numericRows (g : MixedCode) (hg : g.Valid 1 0)
    (R : RotationRows (g.toMultiGraph hg)) (t : ℕ) :
    RotationRows ((g.parallelLabel 0 t).toMultiGraph (UniformParallelCode.validParallel g hg t)) :=
  (UniformParallelCode.incidence g hg t).dartRelabel.rows (RotationRows.redecidable (ParallelSource.rows R t))

theorem parallelRows_getD (rows : Rows) (t v : ℕ) :
    (parallelRows t rows).getD v []=parallelRow t (rows.getD v []) := by
  simp only [parallelRows,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : rows[v]? <;> simp [h,parallelRow]

theorem realizes (g : MixedCode) (hg : g.Valid 1 0) (rows : Rows)
    (R : RotationRows (g.toMultiGraph hg)) (hrows : PlanarityRowFaceCode.Realizes g hg rows R)
    (t : ℕ) :
    PlanarityRowFaceCode.Realizes (g.parallelLabel 0 t) (UniformParallelCode.validParallel g hg t)
      (parallelRows t rows) (numericRows g hg R t) := by
  intro v
  rw [parallelRows_getD,hrows v]
  change parallelRow t ((R.row v).map eraseDart)=
    ((ParallelSource.expand t (R.row v)).map (UniformParallelCode.incidence g hg t).dartRelabel.dart).map eraseDart
  simp only [List.map_map,Function.comp_def,incidence_erase]
  exact (expand_erase (R.row v)).symm

end PlanarHom.PottsParallelRowCorrespondence

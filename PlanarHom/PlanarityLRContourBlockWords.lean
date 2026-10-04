import PlanarHom.PlanarityLRContourRowWords
import PlanarHom.PlanarityLRCyclicBlockInputs

/-! NEW exact cyclic block transport for the geometric rootward input family. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

theorem rotate_flatMap_eq_afterParentInputs {A B : Type*} [DecidableEq A]
    (row : List A) (parent : A) (block : A → List B) (hp : parent∈row)
    (hparent : block parent=[]) :
    (row.rotate (row.idxOf parent)).flatMap block=afterParentInputs row parent block := by
  have hi : row.idxOf parent<row.length := List.idxOf_lt_length_iff.mpr hp
  rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hi),List.flatMap_append,
    List.drop_eq_getElem_cons hi,List.getElem_idxOf hi,List.flatMap_cons,hparent,List.nil_append]
  rfl

/-- Any retained-label predicate that omits the parent excursion has exactly the
literal after-parent expansion used by the geometric lane construction. -/
theorem contour_filter_eq_afterParentInputs (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (parent : Dart (Fin g.edges.length))
    (keep : Dart (Fin g.edges.length) → Bool)
    (hparent : (hostExcursionWord g hg rows parent).filter keep=[]) :
    (orbitPrefix (dfsContourForRows g hg rows)
        (Function.minimalPeriod (dfsContourForRows g hg rows) parent) parent).filter keep =
      afterParentInputs (rows.row ((g.toMultiGraph hg).dartPair parent).1) parent
        (fun b => (hostExcursionWord g hg rows b).filter keep) := by
  rw [contour_word_eq_row_expansion,List.filter_flatMap]
  have h := rotate_flatMap_eq_afterParentInputs
    (rows.row ((g.toMultiGraph hg).dartPair parent).1) parent
    (fun b => (hostExcursionWord g hg rows b).filter keep)
    ((rows.mem _ _).mpr rfl) hparent
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h

theorem idxOf_map_embedding {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a)=xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [List.map_cons,List.idxOf_cons,Lean.Grind.beq_eq_decide_eq,hf.eq_iff,ih]

theorem afterParentInputs_map_equiv {A B C D : Type*} [DecidableEq A] [DecidableEq B]
    (e : A≃B) (f : C → D) (row : List A) (parent : A) (block : A → List C) :
    (afterParentInputs row parent block).map f=
      afterParentInputs (row.map e) (e parent) (fun b => (block (e.symm b)).map f) := by
  simp only [afterParentInputs,idxOf_map_embedding e e.injective,←List.map_drop,←List.map_take,
    List.map_append,List.map_flatMap,List.flatMap_map,Function.comp_def,e.symm_apply_apply]

theorem afterParentInputs_map_embedding {A B C : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (row : List A) (parent : A)
    (block : B → List C) :
    afterParentInputs (row.map f) (f parent) block=
      afterParentInputs row parent (fun a => block (f a)) := by
  simp only [afterParentInputs,idxOf_map_embedding f hf,←List.map_drop,←List.map_take,
    List.flatMap_map]

end PlanarHom.PlanarityLRRealization

import PlanarHom.PlanarityRowFacePrimitives
import PlanarHom.RadialPottsNumericEndpoints

/-! NEW explicit inverse-rotation serialization from the actual supplied row
lists. The program scans the reversed host row. Its correctness refers to the
same typed rows, without choosing a new LR embedding or assuming an algorithm. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsSourceInverseRows
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn
abbrev Rows := PlanarityRowFaceCode.Rows
abbrev rowsCode := PlanarityRowFaceCode.rowsCode
abbrev inputCode := PlanarityRowFaceCode.inputCode

def previous (g : MixedCode) (rows : Rows) (a : PlanarityRotationCode.Dart) :
    PlanarityRotationCode.Dart := rowNext (rows.getD (host g a) []).reverse a

def index (a : PlanarityRotationCode.Dart) : ℕ := 2*a.1+if a.2 then 1 else 0

def unindex (n : ℕ) : PlanarityRotationCode.Dart := (n/2,decide (n%2=1))

def inverseTable (g : MixedCode) (rows : Rows) : List ℕ :=
  (List.range (2*g.edges.length)).map (fun n=>index (previous g rows (unindex n)))

def radialInput (g : MixedCode) (rows : Rows) (k : ℕ) : RadialPotts.Numeric.Input :=
  (g.edges.length,k,inverseTable g rows)

theorem unindex_index (a : PlanarityRotationCode.Dart) : unindex (index a)=a := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [unindex,index] <;> omega

@[simp] theorem index_erase {g : MixedCode} (a : Dart (Fin g.edges.length)) :
    index (eraseDart a)=RadialPotts.Assembly.dartIndex a := rfl

theorem previous_eq_inverse (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
    (hrows : PlanarityRowFaceCode.Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    previous g rows (eraseDart a)=eraseDart (R.rotation.symm a) := by
  let v := ((g.toMultiGraph hg).dartPair a).1
  have ha : a∈R.row v := (R.mem v a).mpr rfl
  have hn : ((R.row v).map (eraseDart (g:=g))).Nodup := (R.nodup v).map (eraseDart_injective g)
  have ham : eraseDart a∈(R.row v).map (eraseDart (g:=g)) := List.mem_map.mpr ⟨a,ha,rfl⟩
  unfold previous
  rw [eraseDart_host g hg a,hrows v]
  rw [rowNext_eq_formPerm _ (List.nodup_reverse.mpr hn) _ (List.mem_reverse.mpr ham),List.formPerm_reverse]
  have hmap := map_formPerm_apply (eraseDart (g:=g)) (eraseDart_injective g)
    (R.row v).reverse (List.nodup_reverse.mpr (R.nodup v)) (List.mem_reverse.mpr ha)
  rw [List.map_reverse,List.formPerm_reverse,List.formPerm_reverse] at hmap
  exact hmap

theorem inverseTable_eq_rotationCode (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
    (hrows : PlanarityRowFaceCode.Realizes g hg rows R) :
    inverseTable g rows=RadialPotts.Numeric.rotationCode R.rotation := by
  apply List.ext_getElem
  · simp [inverseTable,RadialPotts.Numeric.rotationCode]
  · intro i hi hj
    simp only [inverseTable,List.length_map,List.length_range] at hi
    let a := (RadialPotts.Assembly.dartIndexEquiv g.edges.length).symm ⟨i,hi⟩
    have hidx : index (eraseDart a)=i := by
      rw [index_erase,←RadialPotts.Assembly.dartIndexEquiv_val]
      exact congrArg Fin.val ((RadialPotts.Assembly.dartIndexEquiv _).apply_symm_apply ⟨i,hi⟩)
    have hdecode : unindex i=eraseDart a := by rw [←hidx,unindex_index]
    simp only [inverseTable,List.getElem_map,List.getElem_range,
      RadialPotts.Numeric.rotationCode,List.getElem_ofFn]
    rw [hdecode,previous_eq_inverse g hg rows R hrows,index_erase]

theorem radialInput_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
    (hrows : PlanarityRowFaceCode.Realizes g hg rows R) (k : ℕ) :
    radialInput g rows k=RadialPotts.Numeric.input R.rotation k := by
  simp only [radialInput,RadialPotts.Numeric.input,inverseTable_eq_rotationCode g hg rows R hrows]

end PlanarHom.PottsSourceInverseRows

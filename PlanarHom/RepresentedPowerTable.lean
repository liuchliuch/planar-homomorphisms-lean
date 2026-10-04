import PlanarHom.RepresentedProductTables
import PlanarHom.RepresentedRestrictedNormalization
import PlanarHom.RepresentedWordPowers

/-! Typed retained-word metadata has the same concrete bytes as the computed
product table. Its proof restriction supplies no runtime promise-decider. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedPowerTable
open Complexity RepresentedBit
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ} {A B:Fin t→K}

abbrev Row (t:ℕ) := ValidCode P×(ValidCode P×{w:List ℕ//properWord t w})
def encoding (t:ℕ) : BitEncoding (Row P t) :=
  (validEncoding P).prod ((validEncoding P).prod (wordEncoding t))

def normalizer (t:ℕ) : BitEncoding.Normalizer (encoding P t) :=
  BitEncoding.prodNormalizer (BitEncoding.restrictNormalizer _ _ P.normalizer)
    (BitEncoding.prodNormalizer (BitEncoding.restrictNormalizer _ _ P.normalizer)
      (BitEncoding.restrictNormalizer _ _ (BitEncoding.listNormalizer BitEncoding.natNormalizer)))

def erase (r:Row P t) : RepresentedProductTables.Row P := (r.1,(r.2.1,r.2.2.val))
def source (r:Row P t) : K := validValue P r.1
def target (r:Row P t) : K := validValue P r.2.1

def table (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) :
    List (Row P t) :=
  (RepresentedProductTables.representatives P E WA WB m).attach.map
    (fun r=>(r.val.1,(r.val.2.1,⟨r.val.2.2,(RepresentedProductTables.retained_word P E WA WB m r.val r.property).1⟩)))

theorem erase_table (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) :
    (table P E WA WB m).map (erase P)=RepresentedProductTables.representatives P E WA WB m := by
  simp only [table,List.map_map,Function.comp_def,erase]
  exact List.attach_map_subtype_val _

theorem fp_table (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) :
    FP BitEncoding.unaryNat (encoding P t).list (table P E WA WB) := by
  apply (RepresentedProductTables.fp_representatives P E WA WB).transportOutput
  intro m
  have he:=congrArg ((RepresentedProductTables.rowEncoding P).list.encode) (erase_table P E WA WB m)
  exact he.symm.trans (by
    simp only [BitEncoding.list,List.length_map,List.map_map]
    rfl)

theorem table_semantics (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) :
    (table P E WA WB m).map (fun r=>(source P r,target P r))=ExponentProductTables.representatives A B m := by
  have he:=congrArg (List.map (RepresentedProductTables.semanticPair P)) (erase_table P E WA WB m)
  have hm:(table P E WA WB m).map (fun r=>(source P r,target P r))=
      (RepresentedProductTables.representatives P E WA WB m).map (RepresentedProductTables.semanticPair P):=by
    simpa only [List.map_map,Function.comp_def,erase,source,target,RepresentedProductTables.semanticPair] using he
  exact hm.trans (RepresentedProductTables.representatives_semantics P E WA WB m)

theorem table_word_value (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B)
    (m:ℕ) (r:Row P t) (hr:r∈table P E WA WB m) :
    (r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source P r := by
  have hm:erase P r∈(table P E WA WB m).map (erase P):=List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [erase_table] at hm
  exact (RepresentedProductTables.retained_word P E WA WB m (erase P r) hm).2.2.1

end PlanarHom.RepresentedPowerTable

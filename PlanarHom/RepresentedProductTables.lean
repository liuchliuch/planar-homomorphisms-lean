import PlanarHom.RepresentedProductContracts
import PlanarHom.RepresentedDedupTransport
import PlanarHom.ProductRepresentativeSemantics
import PlanarHom.ListContextMachines

/-! Actual represented exponent-product tables. Source/target representatives
and their generating source word are retained through nonzero filtering and
stable semantic-equality deduplication. No injective field-value codec is used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedProductTables
open Complexity RepresentedBit PairProjectionMachines ArithmeticCircuitPrimitives ListDedupMachines
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ} {A B:Fin t→K}

abbrev Row := ValidCode P×(ValidCode P×List ℕ)
def rowEncoding : BitEncoding (Row P) := (validEncoding P).prod ((validEncoding P).prod BitEncoding.nat.list)
def semanticPair (r:Row P) : K×K := (validValue P r.1,validValue P r.2.1)

def row (WA:WordProductMachine P A) (WB:WordProductMachine P B) (p:ℕ×(Fin t→ℕ)) : Row P :=
  (WA.clipped p,(WB.clipped p,RepresentedExponentWords.word p.1 p.2))

theorem fp_row (WA:WordProductMachine P A) (WB:WordProductMachine P B) :
    FP (RepresentedExponentWords.inputEncoding t) (rowEncoding P) (row P WA WB) :=
  WA.fp_clipped.pair (WB.fp_clipped.pair (RepresentedExponentWords.fp_word t))

def products (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) : List (Row P) :=
  (ExponentProductTables.vectors t m).map (fun r=>row P WA WB (m,r))

theorem fp_products (WA:WordProductMachine P A) (WB:WordProductMachine P B) :
    FP BitEncoding.unaryNat (rowEncoding P).list (products P WA WB) :=
  ((fp_id BitEncoding.unaryNat).pair (ExponentProductTables.fp_vectors t)).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat (BitEncoding.nat.vector t)
      (rowEncoding P) (row P WA WB) (fp_row P WA WB))

theorem products_semantics (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) :
    (products P WA WB m).map (semanticPair P)=ExponentProductTables.products A B m := by
  rw [products,List.map_map]
  apply List.map_congr_left
  intro r hr
  exact Prod.ext (WA.clipped_value hr) (WB.clipped_value hr)

def zeroCode : ValidCode P := ⟨P.constant 0,P.constant_valid 0⟩
def nonzero (E:EqualityMachine P) (r:Row P) : Bool := !(E.validTest (r.1,zeroCode P))

theorem nonzero_semantics (E:EqualityMachine P) (r:Row P) :
    nonzero P E r=decide ((semanticPair P r).1≠0) := by
  simp [nonzero,E.validTest_eq,zeroCode,validValue,semanticPair]

theorem fp_nonzero (E:EqualityMachine P) : FP (rowEncoding P) BitEncoding.bool (nonzero P E) :=
  (((fp_fst (validEncoding P) ((validEncoding P).prod BitEncoding.nat.list)).pair
    (fp_const (rowEncoding P) (validEncoding P) (zeroCode P))).comp E.fp_validTest).comp
      (fp_bool_unary BitEncoding.bool Bool.not)

def nonzeroProducts (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) : List (Row P) :=
  (products P WA WB m).filter (nonzero P E)

def representatives (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) (m:ℕ) : List (Row P) :=
  dedupByFirst E.validTest (nonzeroProducts P E WA WB m)

theorem fp_representatives (E:EqualityMachine P) (WA:WordProductMachine P A) (WB:WordProductMachine P B) :
    FP BitEncoding.unaryNat (rowEncoding P).list (representatives P E WA WB) :=
  (((fp_products P WA WB).comp (ListFilterMachines.fp_filter (rowEncoding P) _ (fp_nonzero P E))).comp
    (fp_dedupByFirst (validEncoding P) ((validEncoding P).prod BitEncoding.nat.list) E.validTest E.fp_validTest))

theorem nonzeroProducts_semantics (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) :
    (nonzeroProducts P E WA WB m).map (semanticPair P)=ExponentProductTables.nonzeroProducts A B m := by
  rw [nonzeroProducts,RepresentedDedupTransport.map_filter (semanticPair P) _ (fun p:K×K=>decide (p.1≠0)) (nonzero_semantics P E),
    products_semantics]
  rfl

theorem representatives_semantics (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) :
    (representatives P E WA WB m).map (semanticPair P)=ExponentProductTables.representatives A B m := by
  unfold representatives dedupByFirst
  rw [RepresentedDedupTransport.map_dedup (semanticPair P)
    (fun p=>E.validTest (p.1.1,p.2.1)) (fun p:((K×K)×(K×K))=>decide (p.1.1=p.2.1))
    (fun a b=>E.validTest_eq a.1 b.1),nonzeroProducts_semantics]
  rfl

theorem representatives_sublist (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) :
    (representatives P E WA WB m).Sublist (products P WA WB m) :=
  (dedupByFirst_sublist _ _).trans List.filter_sublist

theorem length_representatives (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) : (representatives P E WA WB m).length≤(m+1)^t := by
  exact (representatives_sublist P E WA WB m).length_le.trans
    (by simpa only [products,List.length_map] using ExponentProductTables.length_vectors t m)

theorem retained_word (E:EqualityMachine P) (WA:WordProductMachine P A)
    (WB:WordProductMachine P B) (m:ℕ) (r:Row P) (hr:r∈representatives P E WA WB m) :
    properWord t r.2.2 ∧ r.2.2.length=m ∧
      (r.2.2.map (RepresentedExponentWords.symbol A)).prod=validValue P r.1 ∧
      (r.2.2.map (RepresentedExponentWords.symbol B)).prod=validValue P r.2.1 := by
  have hp: r∈products P WA WB m:=(representatives_sublist P E WA WB m).subset hr
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hp
  refine ⟨fun i hi=>RepresentedExponentWords.mem_word_bound hi,?_,?_,?_⟩
  · change (RepresentedExponentWords.word m v).length=m
    rw [RepresentedExponentWords.length_word]
    simpa only [min_eq_right (ExponentProductTables.coordinate_le hv _)] using ExponentProductTables.sum_eq hv
  · exact (WA.value (clippedWord (m,v))).symm
  · exact (WB.value (clippedWord (m,v))).symm

end PlanarHom.RepresentedProductTables

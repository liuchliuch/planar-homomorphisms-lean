import PlanarHom.MaterializedExponentProductMachines
import PlanarHom.ProductRepresentativeSemantics

/-! Total dynamic source/target product-table compilation with exact original row order. -/
namespace PlanarHom.MaterializedProductTableMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines ListDedupMachines
open scoped BigOperators
variable {K : Type} [Field K] {t : ℕ}

abbrev Input (K : Type) (t : ℕ) := ℕ × ((Fin t → K) × (Fin t → K))

/-- Use the existing weak exponent enumeration and exact product-table semantics. -/
def products (p : Input K t) : List (K × K) := ExponentProductTables.products p.2.1 p.2.2 p.1

variable [DecidableEq K]

/-- Retain nonzero source rows before stable source-key collision merging. -/
def nonzeroProducts (p : Input K t) : List (K × K) :=
  ExponentProductTables.nonzeroProducts p.2.1 p.2.2 p.1

def representatives (p : Input K t) : List (K × K) :=
  ExponentProductTables.representatives p.2.1 p.2.2 p.1

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- Literal unary m followed by two original canonical vectors of fixed dimension. -/
noncomputable def inputEncoding (t : ℕ) : BitEncoding (Input K t) :=
  BitEncoding.unaryNat.prod (((numberFieldEncoding basis).vector t).prod ((numberFieldEncoding basis).vector t))

omit [DecidableEq K] in
theorem fp_product_pair : FP ((inputEncoding basis t).prod (BitEncoding.nat.vector t))
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (fun p : Input K t × (Fin t → ℕ) =>
      (∏ i, p.1.2.1 i ^ min p.1.1 (p.2 i), ∏ i, p.1.2.2 i ^ min p.1.1 (p.2 i))) := by
  have hp := fp_fst (inputEncoding basis t) (BitEncoding.nat.vector t)
  have hr := fp_snd (inputEncoding basis t) (BitEncoding.nat.vector t)
  have hm := hp.comp (fp_fst BitEncoding.unaryNat
    (((numberFieldEncoding basis).vector t).prod ((numberFieldEncoding basis).vector t)))
  have hv := hp.comp (fp_snd BitEncoding.unaryNat
    (((numberFieldEncoding basis).vector t).prod ((numberFieldEncoding basis).vector t)))
  have ha := hv.comp (fp_fst ((numberFieldEncoding basis).vector t) ((numberFieldEncoding basis).vector t))
  have hb := hv.comp (fp_snd ((numberFieldEncoding basis).vector t) ((numberFieldEncoding basis).vector t))
  exact ((hm.pair (ha.pair hr)).comp (MaterializedExponentProductMachines.fp_product basis)).pair
    ((hm.pair (hb.pair hr)).comp (MaterializedExponentProductMachines.fp_product basis))

omit [DecidableEq K] in
/-- Enumerate weak exponent vectors and evaluate both materialized vectors on every
row by real FP machines. The unary cap is exact on every enumerated coordinate. -/
theorem fp_products : FP (inputEncoding basis t)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list (products : Input K t → List (K × K)) := by
  have hm := fp_fst BitEncoding.unaryNat
    (((numberFieldEncoding basis).vector t).prod ((numberFieldEncoding basis).vector t))
  have hv := hm.comp (ExponentProductTables.fp_vectors t)
  have hmap := ListContextMachines.fp_mapWithContext (inputEncoding basis t) (BitEncoding.nat.vector t)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) _ (fp_product_pair basis)
  have h := ((fp_id (inputEncoding basis t)).pair hv).comp hmap
  apply h.congr
  intro p
  apply List.map_congr_left
  intro r hr
  change (∏ i, p.2.1 i ^ min p.1 (r i), ∏ i, p.2.2 i ^ min p.1 (r i)) =
    (∏ i, p.2.1 i ^ r i, ∏ i, p.2.2 i ^ r i)
  rw [FixedExponentProductMachines.clipped_product_eq p.2.1 p.1 r (ExponentProductTables.coordinate_le hr),
    FixedExponentProductMachines.clipped_product_eq p.2.2 p.1 r (ExponentProductTables.coordinate_le hr)]

theorem fp_nonzeroProducts : FP (inputEncoding basis t)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
    (nonzeroProducts : Input K t → List (K × K)) := by
  let e := numberFieldEncoding basis
  have heq := ((fp_fst e e).pair (fp_const (e.prod e) e (0 : K))).comp (FixedFieldArithmetic.fp_equality basis)
  have hne : FP (e.prod e) BitEncoding.bool (fun p : K × K => decide (p.1 ≠ 0)) :=
    (heq.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun _ => by simp)
  exact (fp_products basis).comp (ListFilterMachines.fp_filter (e.prod e) _ hne)

/-- Stable first source-key representatives keep their original target products;
there is no fixed source alphabet or promised input subtype. -/
theorem fp_representatives : FP (inputEncoding basis t)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
    (representatives : Input K t → List (K × K)) :=
  (fp_nonzeroProducts basis).comp (fp_dedupByFirst (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun p : K × K => decide (p.1 = p.2)) (FixedFieldArithmetic.fp_equality basis))

omit [Algebra ℚ K] [DecidableEq K] in
theorem length_products (p : Input K t) : (products p).length ≤ (p.1 + 1) ^ t :=
  ExponentProductTables.length_products _ _ _

omit [Algebra ℚ K] in
theorem representatives_sublist (p : Input K t) : (representatives p).Sublist (products p) :=
  ExponentProductTables.representatives_sublist _ _ _

omit [Algebra ℚ K] in
theorem length_representatives (p : Input K t) : (representatives p).length ≤ (p.1 + 1) ^ t :=
  ExponentProductTables.representatives_length _ _ _

omit [Algebra ℚ K] in
theorem representatives_nonzero (p : Input K t) (row : K × K) (hrow : row ∈ representatives p) : row.1 ≠ 0 :=
  ExponentProductTables.representatives_nonzero _ _ _ row hrow

omit [Algebra ℚ K] in
theorem representatives_pairwise (p : Input K t) :
    (representatives p).Pairwise (fun row row' => row.1 ≠ row'.1) :=
  ExponentProductTables.representatives_pairwise _ _ _

omit [Algebra ℚ K] in
theorem representatives_coverage (p : Input K t) (row : K × K) (hrow : row ∈ products p) (hz : row.1 ≠ 0) :
    ∃ row' ∈ representatives p, row.1 = row'.1 :=
  ExponentProductTables.representatives_coverage _ _ _ row hrow hz

omit [Algebra ℚ K] in
/-- Stable merging retains the earliest original row for each source key. -/
theorem first_representative_mem (p : Input K t) (before after : List (K × K)) (row : K × K)
    (hrows : nonzeroProducts p = before ++ row :: after)
    (hfirst : ∀ row' ∈ before, row.1 ≠ row'.1) : row ∈ representatives p := by
  change row ∈ dedup (fun q : (K × K) × (K × K) => decide (q.1.1 = q.2.1)) (nonzeroProducts p)
  rw [hrows]
  apply ListDedupMachines.first_representative_mem
  intro row' hrow' hrel
  exact hfirst row' hrow' (of_decide_eq_true hrel)

/-- The computed table words themselves have polynomial size in the literal input. -/
theorem exists_table_encoding_bound : ∃ p : Polynomial ℕ, ∀ x : Input K t,
    (((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list.encode (representatives x)).length ≤
      p.eval ((inputEncoding basis t).encode x).length := by
  obtain ⟨computer⟩ := fp_representatives (t := t) basis
  exact ⟨MachineComposition.outputLengthPolynomial computer,
    fun x => MachineComposition.encoded_output_length_le computer x⟩

end PlanarHom.MaterializedProductTableMachines

import PlanarHom.BooleanGroupedTableRecoveryMachines
import PlanarHom.BooleanFieldCollisionMachines
import PlanarHom.ExponentVectorMachines
import PlanarHom.DependentMonomialMachines
import PlanarHom.ListReverseMachines

/-! Concrete grouped-interpolation metadata from the unary source length and
one exact rational sample.  The full fixed-dimensional box is materialized and
clipped coordinatewise.  Its repeated nodes are deliberately retained; neither
comparison of radical values nor a source-evaluation oracle is used. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanGroupedMetadataMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BooleanFieldTower BooleanFieldCollision
variable {K : Type} [Field K] [Algebra ℚ K] {dimension b : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Input := ℕ × ℚ
def inputEncoding : BitEncoding Input := BitEncoding.unaryNat.prod BitEncoding.rat
abbrev Node (K : Type) (b : ℕ) := BooleanGroupedTableRecoveryMachines.Node K b
abbrev Metadata (K : Type) (b : ℕ) :=
  List K × (List (Node K b) × List (Tower K b))

def metadataEncoding (b : ℕ) : BitEncoding (Metadata K b) :=
  (numberFieldEncoding basis).list.prod
    ((BooleanGroupedTableRecoveryMachines.nodeEncoding basis b).list.prod
      (BooleanFieldTowerMachines.encoding basis b).list)

def counts (d : Fin b → ℕ) (p : Input) (i : Fin b) : ℕ := d i * p.1
def cap (d : Fin b → ℕ) (p : Input) : ℕ := (∑ i, d i) * p.1
def clipped (d : Fin b → ℕ) (p : Input) (ks : List ℕ) (i : Fin b) : ℕ :=
  min (counts d p i) (ks.getD i.val 0)

def radicandList (a w : Fin b → K) (p : Input) : List K :=
  List.ofFn (fun i : Fin b => radicands a w (algebraMap ℚ K p.2) i.val)

def node (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input × List ℕ) : Node K b :=
  (clipped d p.1 p.2 g0,
    spectral c a w (algebraMap ℚ K p.1.2) (counts d p.1) (clipped d p.1 p.2))

def nodes (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) (p : Input) :
    List (Node K b) :=
  (ExponentVectors.box b (cap d p)).map (fun ks => node c a w d g0 (p,ks))

/-- Only the retained coordinate contributes.  Clipping makes the raw target
machine total, while its enumerated arguments are already in range. -/
def target (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input × ℕ) : Tower K b :=
  let D := radicands a w (algebraMap ℚ K p.1.2)
  let r := min (counts d p.1 g0) p.2
  mul D b (power D b (linear b g0 (c g0) 1) (counts d p.1 g0-r))
    (power D b (linear b g0 (c g0) (-1)) r)

/-- Ascending order is essential: recovery labels these targets by `zipIdx`. -/
def targets (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) (p : Input) :
    List (Tower K b) :=
  (List.range (counts d p g0+1)).map (fun r => target c a w d g0 (p,r))

def metadata (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) (p : Input) :
    Metadata K b := (radicandList a w p, (nodes c a w d g0 p, targets c a w d g0 p))

/-- Append the literal positive-moment answer list without changing any
metadata or supplying a hidden zeroth-moment query. -/
def attachAnswers (p : Metadata K b × List K) :
    BooleanGroupedTableRecoveryMachines.Input K b :=
  (p.1.1, (p.1.2.1, (p.1.2.2, p.2)))

theorem fp_counts (d : Fin b → ℕ) (i : Fin b) :
    FP inputEncoding BitEncoding.unaryNat (fun p => counts d p i) :=
  ((fp_fst BitEncoding.unaryNat BitEncoding.rat).comp
    (UnaryPolynomialMachines.fp_eval (Polynomial.C (d i)*Polynomial.X))).congr
      (fun _ => by simp [counts])

theorem fp_cap (d : Fin b → ℕ) : FP inputEncoding BitEncoding.unaryNat (cap d) :=
  ((fp_fst BitEncoding.unaryNat BitEncoding.rat).comp
    (UnaryPolynomialMachines.fp_eval (Polynomial.C (∑ i, d i)*Polynomial.X))).congr
      (fun _ => by simp only [Function.comp_apply, cap, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X])

theorem fp_radicandList (a w : Fin b → K) :
    FP inputEncoding (numberFieldEncoding basis).list (radicandList a w) := by
  have hx := (fp_snd BitEncoding.unaryNat BitEncoding.rat).comp
    (FixedFieldPolynomialMachines.fp_ratCast basis)
  have hv := FixedVectorMachines.fp_assemble inputEncoding (numberFieldEncoding basis) b
    (fun p i => radicands a w (algebraMap ℚ K p.2) i.val)
    (fun i => BooleanFieldCollisionMachines.fp_radicands basis inputEncoding a w _ hx i.val)
  have hl : FP ((numberFieldEncoding basis).vector b) (numberFieldEncoding basis).list
      (List.ofFn : (Fin b → K) → List K) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp hl

theorem fp_clipped (d : Fin b → ℕ) (i : Fin b) :
    FP (inputEncoding.prod BitEncoding.nat.list) BitEncoding.unaryNat
      (fun p : Input × List ℕ => clipped d p.1 p.2 i) := by
  have hn := (fp_fst inputEncoding BitEncoding.nat.list).comp (fp_counts d i)
  have hk := (fp_snd inputEncoding BitEncoding.nat.list).comp
    (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val)
  exact (hn.pair hk).comp ⟨BoundedUnaryMachines.computer⟩

theorem fp_node (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) :
    FP (inputEncoding.prod BitEncoding.nat.list)
      (BooleanGroupedTableRecoveryMachines.nodeEncoding basis b) (node c a w d g0) := by
  have hp := fp_fst inputEncoding BitEncoding.nat.list
  have hx := (hp.comp (fp_snd BitEncoding.unaryNat BitEncoding.rat)).comp
    (FixedFieldPolynomialMachines.fp_ratCast basis)
  have hs := BooleanFieldCollisionMachines.fp_spectral basis
    (inputEncoding.prod BitEncoding.nat.list) c a w _ _ _ hx
    (fun i => hp.comp (fp_counts d i)) (fp_clipped d)
  exact ((fp_clipped d g0).comp UnaryNatConversionMachine.fp_conversion).pair hs

theorem fp_nodes (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) :
    FP inputEncoding (BooleanGroupedTableRecoveryMachines.nodeEncoding basis b).list
      (nodes c a w d g0) :=
  ((fp_id inputEncoding).pair ((fp_cap d).comp (ExponentVectorMachines.fp_box b))).comp
    (ListContextMachines.fp_mapWithContext inputEncoding BitEncoding.nat.list
      (BooleanGroupedTableRecoveryMachines.nodeEncoding basis b) _ (fp_node basis c a w d g0))

theorem fp_target (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) :
    FP (inputEncoding.prod BitEncoding.nat) (BooleanFieldTowerMachines.encoding basis b)
      (target c a w d g0) := by
  let e := inputEncoding.prod BitEncoding.nat
  have hp := fp_fst inputEncoding BitEncoding.nat
  have hx := (hp.comp (fp_snd BitEncoding.unaryNat BitEncoding.rat)).comp
    (FixedFieldPolynomialMachines.fp_ratCast basis)
  let D := fun p : Input × ℕ => radicands a w (algebraMap ℚ K p.1.2)
  have hD : ∀ i, FP e (numberFieldEncoding basis) (fun p => D p i) :=
    BooleanFieldCollisionMachines.fp_radicands basis e a w _ hx
  have hn := hp.comp (fp_counts d g0)
  have hr : FP e BitEncoding.unaryNat
      (fun p : Input × ℕ => min (counts d p.1 g0) p.2) :=
    (hn.pair (fp_snd inputEncoding BitEncoding.nat)).comp ⟨BoundedUnaryMachines.computer⟩
  have hc := fp_const e (numberFieldEncoding basis) (c g0)
  exact BooleanFieldTowerMachines.fp_mul basis e D hD b _ _
    (BooleanFieldCollisionMachines.fp_power_linear_plus basis e D hD b g0 _ _ hc
      (BooleanFieldCollisionMachines.fp_unary_sub e _ _ hn hr))
    (BooleanFieldCollisionMachines.fp_power_linear_minus basis e D hD b g0 _ _ hc hr)

theorem fp_targets (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) :
    FP inputEncoding (BooleanFieldTowerMachines.encoding basis b).list
      (targets c a w d g0) := by
  have hr : FP inputEncoding BitEncoding.nat.list
      (fun p => List.range (counts d p g0+1)) :=
    ((((fp_counts d g0).comp (UnaryPolynomialMachines.fp_eval (Polynomial.X+1))).comp
      UnaryRangeMachines.fp_range).comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
        (fun _ => by simp)
  exact ((fp_id inputEncoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext inputEncoding BitEncoding.nat
      (BooleanFieldTowerMachines.encoding basis b) _ (fp_target basis c a w d g0))

/-- The preprocessing theorem has no height, oracle, or supplied evaluator
premise. Every variable power is fed a physically bounded unary exponent. -/
theorem fp_metadata (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) :
    FP inputEncoding (metadataEncoding basis b) (metadata c a w d g0) :=
  (fp_radicandList basis a w).pair
    ((fp_nodes basis c a w d g0).pair (fp_targets basis c a w d g0))

theorem fp_attachAnswers (b : ℕ) :
    FP ((metadataEncoding basis b).prod (numberFieldEncoding basis).list)
      (BooleanGroupedTableRecoveryMachines.inputEncoding basis b) (attachAnswers (b := b)) := by
  let ed := (numberFieldEncoding basis).list
  let en := (BooleanGroupedTableRecoveryMachines.nodeEncoding basis b).list
  let et := (BooleanFieldTowerMachines.encoding basis b).list
  have hp := fp_fst (metadataEncoding basis b) ed
  have hd := hp.comp (fp_fst ed (en.prod et))
  have hnt := hp.comp (fp_snd ed (en.prod et))
  exact hd.pair ((hnt.comp (fp_fst en et)).pair
    ((hnt.comp (fp_snd en et)).pair (fp_snd (metadataEncoding basis b) ed)))

theorem counts_le_cap (d : Fin b → ℕ) (p : Input) (i : Fin b) :
    counts d p i ≤ cap d p :=
  Nat.mul_le_mul_right p.1
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

theorem clipped_le (d : Fin b → ℕ) (p : Input) (ks : List ℕ) (i : Fin b) :
    clipped d p ks i ≤ counts d p i := min_le_left _ _

theorem clipped_ofFn (d : Fin b → ℕ) (p : Input) (k : Fin b → ℕ)
    (hk : ∀ i, k i ≤ counts d p i) : clipped d p (List.ofFn k) = k := by
  funext i
  simp only [clipped]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]
  exact min_eq_right (hk i)

theorem ofFn_mem_box (d : Fin b → ℕ) (p : Input) (k : Fin b → ℕ)
    (hk : ∀ i, k i ≤ counts d p i) : List.ofFn k ∈ ExponentVectors.box b (cap d p) := by
  apply (ExponentVectors.mem_box _ _ _).mpr
  refine ⟨List.length_ofFn, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact (hk i).trans (counts_le_cap d p i)

/-- Every bounded count vector occurs, even when clipping creates repeats. -/
theorem node_mem (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (k : Fin b → ℕ) (hk : ∀ i, k i ≤ counts d p i) :
    (k g0, spectral c a w (algebraMap ℚ K p.2) (counts d p) k) ∈ nodes c a w d g0 p := by
  apply List.mem_map.mpr
  refine ⟨List.ofFn k, ofFn_mem_box d p k hk, ?_⟩
  simp only [node, clipped_ofFn d p k hk]

/-- Conversely every emitted node is exactly a bounded source product with
the retained-coordinate group label. -/
theorem mem_nodes_iff (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (z : Node K b) : z ∈ nodes c a w d g0 p ↔
      ∃ k : Fin b → ℕ, (∀ i, k i ≤ counts d p i) ∧
        z = (k g0, spectral c a w (algebraMap ℚ K p.2) (counts d p) k) := by
  constructor
  · intro hz
    obtain ⟨ks, _, rfl⟩ := List.mem_map.mp hz
    exact ⟨clipped d p ks, clipped_le d p ks, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact node_mem c a w d g0 p k hk

theorem node_label_le (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (z : Node K b) (hz : z ∈ nodes c a w d g0 p) : z.1 ≤ counts d p g0 := by
  obtain ⟨k, hk, rfl⟩ := (mem_nodes_iff c a w d g0 p z).mp hz
  exact hk g0

@[simp] theorem length_nodes (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) : (nodes c a w d g0 p).length = (cap d p+1)^b := by
  simp [nodes, ExponentVectors.length_box]

theorem length_nodes_le (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) : (nodes c a w d g0 p).length ≤ (cap d p+1)^b :=
  le_of_eq (length_nodes c a w d g0 p)

@[simp] theorem length_radicandList (a w : Fin b → K) (p : Input) :
    (radicandList a w p).length = b := List.length_ofFn

@[simp] theorem radicandList_getD (a w : Fin b → K) (p : Input) (i : ℕ) :
    (radicandList a w p).getD i 0 = radicands a w (algebraMap ℚ K p.2) i := by
  by_cases hi : i < b
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [radicandList, List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    simp [radicands, extend, hi]

theorem target_eq (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (r : ℕ) (hr : r ≤ counts d p g0) :
    target c a w d g0 (p,r) =
      mul (radicands a w (algebraMap ℚ K p.2)) b
        (power (radicands a w (algebraMap ℚ K p.2)) b
          (linear b g0 (c g0) 1) (counts d p g0-r))
        (power (radicands a w (algebraMap ℚ K p.2)) b
          (linear b g0 (c g0) (-1)) r) := by
  simp only [target, min_eq_right hr]

@[simp] theorem length_targets (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) : (targets c a w d g0 p).length = counts d p g0+1 := by
  simp [targets]

theorem targets_getElem (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (r : ℕ) (hr : r < (targets c a w d g0 p).length) :
    (targets c a w d g0 p)[r] = target c a w d g0 (p,r) := by
  simp [targets]

theorem target_mem (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (r : ℕ) (hr : r ≤ counts d p g0) :
    target c a w d g0 (p,r) ∈ targets c a w d g0 p :=
  List.mem_map.mpr ⟨r, List.mem_range.mpr (Nat.lt_succ_of_le hr), rfl⟩

theorem node_label_lt_targets (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (z : Node K b) (hz : z ∈ nodes c a w d g0 p) :
    z.1 < (targets c a w d g0 p).length := by
  rw [length_targets]
  exact Nat.lt_succ_of_le (node_label_le c a w d g0 p z hz)

/-- The node coefficient tuple represents the literal product of the signed
linear eigenvalue factors in the formal commutative algebra. -/
theorem node_value_spectral (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (ks : List ℕ) :
    let D := radicands a w (algebraMap ℚ K p.2)
    BooleanFieldTowerAlgebra.ofTower D b (node c a w d g0 (p,ks)).2 =
      ∏ i : Fin b,
        (BooleanFieldTowerAlgebra.ofTower D b (linear b i (c i) 1)) ^
          (counts d p i-clipped d p ks i) *
        (BooleanFieldTowerAlgebra.ofTower D b (linear b i (c i) (-1))) ^
          (clipped d p ks i) := by
  simp only [BooleanFieldTowerAlgebra.ofTower, BooleanFieldTowerAlgebra.product_eq,
    BooleanFieldTowerAlgebra.pow_eq, BooleanFieldTowerAlgebra.mul_eq, node, spectral]

/-- The target represents exactly the retained factor; all other coordinates
contribute the multiplicative identity. -/
theorem target_value_retained (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (r : ℕ) (hr : r ≤ counts d p g0) :
    let D := radicands a w (algebraMap ℚ K p.2)
    BooleanFieldTowerAlgebra.ofTower D b (target c a w d g0 (p,r)) =
      (BooleanFieldTowerAlgebra.ofTower D b (linear b g0 (c g0) 1)) ^
        (counts d p g0-r) *
      (BooleanFieldTowerAlgebra.ofTower D b (linear b g0 (c g0) (-1))) ^ r := by
  simp only [BooleanFieldTowerAlgebra.ofTower, BooleanFieldTowerAlgebra.pow_eq,
    BooleanFieldTowerAlgebra.mul_eq, target_eq c a w d g0 p r hr]

@[simp] theorem length_nodes_zero (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (q : ℚ) : (nodes c a w d g0 (0,q)).length = 1 := by
  simp [cap]

@[simp] theorem length_targets_zero (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (q : ℚ) : (targets c a w d g0 (0,q)).length = 1 := by
  simp [counts]

theorem target_zero_count (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (r : ℕ) (hn : counts d p g0 = 0) :
    target c a w d g0 (p,r) = embed b 1 := by
  simp only [target, hn, Nat.zero_min, Nat.sub_self, power, ← embed_mul, one_mul]

theorem targets_zero_count (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b)
    (p : Input) (hn : counts d p g0 = 0) :
    targets c a w d g0 p = [embed b 1] := by
  simp [targets, hn, target_zero_count c a w d g0 p 0 hn]

end PlanarHom.BooleanGroupedMetadataMachines

import PlanarHom.ExponentProductTableMachines
import PlanarHom.ExponentProductSemantics
import PlanarHom.ListDedupMachines

/-! Actual nonzero filtering and stable source-key collision merging of the
computed source/target product table. Target entries remain original products. -/
namespace PlanarHom.ExponentProductTables
open Turing PlanarHom.Complexity PlanarHom.ListDedupMachines
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension t : ℕ}

def nonzeroProducts (A B : Fin t→K) (m : ℕ) : List (K × K):=
  (products A B m).filter (fun p=>decide (p.1≠0))

def representatives (A B : Fin t→K) (m : ℕ) : List (K × K):=
  dedupByFirst (fun p : K × K=>decide (p.1=p.2)) (nonzeroProducts A B m)

omit [Algebra ℚ K] [Field K] in
private theorem equality_equivalence : Equivalence (ListDedupMachines.Rel (fun p : K × K=>decide (p.1=p.2))):=by
  constructor
  · intro x
    exact decide_eq_true rfl
  · intro x y h
    exact decide_eq_true (of_decide_eq_true h).symm
  · intro x y z h₁ h₂
    exact decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂))

omit [Algebra ℚ K] in
theorem representatives_sublist (A B : Fin t→K) (m : ℕ) :
    (representatives A B m).Sublist (products A B m):=
  (dedupByFirst_sublist _ _).trans List.filter_sublist

omit [Algebra ℚ K] in
theorem representatives_length (A B : Fin t→K) (m : ℕ) :
    (representatives A B m).length≤(m+1)^t:=
  (representatives_sublist A B m).length_le.trans (length_products A B m)

omit [Algebra ℚ K] in
theorem representatives_nonzero (A B : Fin t→K) (m : ℕ) (p : K × K)
    (hp : p∈representatives A B m) : p.1≠0:=by
  have hm: p∈nonzeroProducts A B m:=(dedupByFirst_sublist _ _).subset hp
  exact of_decide_eq_true (List.mem_filter.mp hm).2

omit [Algebra ℚ K] in
theorem representatives_coverage (A B : Fin t→K) (m : ℕ) (p : K × K)
    (hp : p∈products A B m) (hz : p.1≠0) :
    ∃q∈representatives A B m,p.1=q.1:=by
  have hmem:p∈nonzeroProducts A B m:=List.mem_filter.mpr ⟨hp,by simpa⟩
  obtain ⟨q,hq,he⟩:=dedupByFirst_coverage _ equality_equivalence (nonzeroProducts A B m) p hmem
  exact ⟨q,hq,of_decide_eq_true he⟩

omit [Algebra ℚ K] in
theorem representatives_pairwise (A B : Fin t→K) (m : ℕ) :
    (representatives A B m).Pairwise (fun p q=>p.1≠q.1):=by
  simpa only [ListDedupMachines.Rel,decide_eq_true_eq] using
    dedupByFirst_pairwise (fun p : K × K=>decide (p.1=p.2)) equality_equivalence (nonzeroProducts A B m)

theorem fp_representatives (basis : Module.Basis (Fin dimension) ℚ K) (A B : Fin t→K) :
    FP BitEncoding.unaryNat ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
      (representatives A B):=by
  let e:=numberFieldEncoding basis
  have heq:=((PairProjectionMachines.fp_fst e e).pair (fp_const (e.prod e) e 0)).comp
    (PlanarHom.FixedFieldArithmetic.fp_equality basis)
  have hne : FP (e.prod e) BitEncoding.bool (fun p : K × K=>decide (p.1≠0)):=by
    exact (heq.comp (PlanarHom.ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool Bool.not)).congr
      (fun p=>by simp)
  have hn:=(fp_products basis A B).comp (PlanarHom.ListFilterMachines.fp_filter (e.prod e) _ hne)
  exact hn.comp (fp_dedupByFirst e e (fun p : K × K=>decide (p.1=p.2))
    (PlanarHom.FixedFieldArithmetic.fp_equality basis))

end PlanarHom.ExponentProductTables

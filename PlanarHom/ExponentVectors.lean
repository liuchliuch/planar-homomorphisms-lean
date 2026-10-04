import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lean.Elab.Tactic.Omega

/-! Explicit bounded exponent-vector enumeration for fixed constraint arity.
This module proves the finite enumeration and cardinality invariants; its
machine realization is kept separate. -/
namespace PlanarHom.ExponentVectors

/-- The order matches the actual descending unary-range enumerator. -/
def box : ℕ→ℕ→List (List ℕ)
  | 0,_=>[[]]
  | t+1,m=>(List.range (m+1)).reverse.flatMap (fun a=>(box t m).map (List.cons a))

/-- Retain exactly those vectors describing a product with `m` occurrences. -/
def weak (t m : ℕ) : List (List ℕ):=(box t m).filter (fun xs=>decide (xs.sum=m))

theorem mem_box (t m : ℕ) (xs : List ℕ) :
    xs∈box t m ↔ xs.length=t ∧ ∀a∈xs,a≤m:=by
  induction t generalizing xs with
  | zero=>cases xs <;> simp [box]
  | succ t ih=>
    cases xs with
    | nil=>simp [box]
    | cons a xs=>
      simp only [box,List.mem_flatMap,List.mem_reverse,List.mem_range,List.mem_map,List.cons.injEq,
        List.length_cons,List.forall_mem_cons,Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨b,hb,ys,hys,hba,hysx⟩
        subst b; subst ys
        obtain ⟨hlen,hbound⟩:= (ih xs).mp hys
        exact ⟨hlen,by omega,hbound⟩
      · rintro ⟨hlen,ha,hrest⟩
        exact ⟨a,by omega,xs,(ih xs).mpr ⟨hlen,hrest⟩,rfl,rfl⟩

theorem length_box (t m : ℕ) : (box t m).length=(m+1)^t:=by
  induction t with
  | zero=>simp [box]
  | succ t ih=>
    simp [box,List.length_flatMap,ih,pow_succ,Nat.mul_comm]

private theorem le_sum_of_mem (a : ℕ) (xs : List ℕ) (h : a∈xs) : a≤xs.sum:=by
  induction xs with
  | nil=>simp at h
  | cons b xs ih=>
    rcases List.mem_cons.mp h with rfl | ha
    · simp
    · have hh:=ih ha; simp only [List.sum_cons]; omega

theorem mem_weak (t m : ℕ) (xs : List ℕ) : xs∈weak t m ↔ xs.length=t ∧ xs.sum=m:=by
  simp only [weak,List.mem_filter,decide_eq_true_eq,mem_box]
  constructor
  · rintro ⟨⟨hlen,_⟩,hsum⟩; exact ⟨hlen,hsum⟩
  · rintro ⟨hlen,hsum⟩
    exact ⟨⟨hlen,fun a ha=>by rw [←hsum]; exact le_sum_of_mem a xs ha⟩,hsum⟩

theorem length_weak_le (t m : ℕ) : (weak t m).length≤(m+1)^t:=by
  exact (List.length_filter_le _ _).trans_eq (length_box t m)

theorem coordinate_le {t m a : ℕ} {xs : List ℕ} (h : xs∈weak t m) (ha : a∈xs) : a≤m:=by
  have hs:xs.sum=m:=((mem_weak t m xs).mp h).2
  simpa only [hs] using le_sum_of_mem a xs ha

/-- Filtering does not invent a vector; this is useful for product evaluation
and later exact collision merging. -/
theorem weak_sublist (t m : ℕ) : List.Sublist (weak t m) (box t m):=List.filter_sublist

end PlanarHom.ExponentVectors

import PlanarHom.FisherParityPath
import PlanarHom.FisherIncidenceOrdering

/-! The local path with two endpoint loops used for cubic degree reduction. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher

def pathLoopVertex (d : ℕ) (b : Bool) : Fin (d + 2) :=
  if b then Fin.last (d + 1) else 0

/-- There are d interior port vertices and two endpoint vertices. Path edges
connect successive vertices; each endpoint has one loop occurrence. -/
def localExpansion (d : ℕ) : MultiGraph (Fin (d + 2)) (Fin (d + 1) ⊕ Bool) where
  src := Sum.elim Fin.castSucc (pathLoopVertex d)
  dst := Sum.elim Fin.succ (pathLoopVertex d)

@[simp] theorem pathLoopVertex_eq_zero (d : ℕ) (b : Bool) :
    pathLoopVertex d b = 0 ↔ b = false := by
  cases b <;> simp [pathLoopVertex, Fin.ext_iff]

@[simp] theorem pathLoopVertex_eq_last (d : ℕ) (b : Bool) :
    pathLoopVertex d b = Fin.last (d + 1) ↔ b = true := by
  cases b <;> simp [pathLoopVertex, Fin.ext_iff]

theorem pathLoopVertex_ne_interior {d : ℕ} (b : Bool) (i : Fin d) :
    pathLoopVertex d b ≠ i.succ.castSucc := by
  cases b
  · intro h
    have hv := congrArg Fin.val h
    change 0 = i.val + 1 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change d + 1 = i.val + 1 at hv
    omega

theorem local_degree_zero {d : ℕ} (P : Finset (Fin (d + 1))) (L : Finset Bool) :
    (localExpansion d).selectedDegree (P.disjSum L) 0 =
      (if (0 : Fin (d + 1)) ∈ P then 1 else 0) +
        2 * (if false ∈ L then 1 else 0) := by
  simp only [MultiGraph.selectedDegree, Finset.sum_disjSum, localExpansion,
    Sum.elim_inl, Sum.elim_inr]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  split_ifs <;> rfl

theorem local_degree_last {d : ℕ} (P : Finset (Fin (d + 1))) (L : Finset Bool) :
    (localExpansion d).selectedDegree (P.disjSum L) (Fin.last (d + 1)) =
      (if Fin.last d ∈ P then 1 else 0) +
        2 * (if true ∈ L then 1 else 0) := by
  simp only [MultiGraph.selectedDegree, Finset.sum_disjSum, localExpansion,
    Sum.elim_inl, Sum.elim_inr, ← Fin.succ_last]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  split_ifs <;> rfl

theorem local_degree_interior {d : ℕ} (P : Finset (Fin (d + 1))) (L : Finset Bool)
    (i : Fin d) :
    (localExpansion d).selectedDegree (P.disjSum L) i.succ.castSucc =
      (if i.castSucc ∈ P then 1 else 0) + (if i.succ ∈ P then 1 else 0) := by
  simp only [MultiGraph.selectedDegree, Finset.sum_disjSum, localExpansion,
    Sum.elim_inl, Sum.elim_inr]
  have hs (k : Fin (d + 1)) : k.castSucc = i.succ.castSucc ↔ k = i.succ := by
    exact Fin.castSucc_inj
  have hd (k : Fin (d + 1)) : k.succ = i.succ.castSucc ↔ k = i.castSucc := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      change k.val + 1 = i.val + 1 at hv
      change k.val = i.val
      omega
    · rintro rfl
      rfl
  simp only [hs, hd, pathLoopVertex_ne_interior, ↓reduceIte, add_zero,
    Finset.sum_const_zero, Finset.sum_add_distrib]
  simp [Nat.add_comm]

/-- Add the one original incidence attached at each interior port. -/
def LocalEven {d : ℕ} (a : Fin d → Bool) (P : Finset (Fin (d + 1)))
    (L : Finset Bool) : Prop :=
  Even ((localExpansion d).selectedDegree (P.disjSum L) 0) ∧
  Even ((localExpansion d).selectedDegree (P.disjSum L) (Fin.last (d + 1))) ∧
  ∀ i, Even ((localExpansion d).selectedDegree (P.disjSum L) i.succ.castSucc +
    (if a i then 1 else 0))

theorem even_three_bits (a b c : Bool) :
    Even ((if a then 1 else 0 : ℕ) + (if b then 1 else 0) + (if c then 1 else 0)) ↔
      b = Bool.xor a c := by
  revert a b c
  decide +kernel

/-- Endpoint loops do not affect parity; the path bits satisfy the exact XOR
recurrence. This includes the d=0 path between the two looped endpoints. -/
theorem localEven_iff_parityPath {d : ℕ} (a : Fin d → Bool)
    (P : Finset (Fin (d + 1))) (L : Finset Bool) :
    LocalEven a P L ↔ ParityPath a (fun i => decide (i ∈ P)) := by
  simp only [LocalEven, local_degree_zero, local_degree_last, local_degree_interior,
    ParityPath]
  have he (b : Bool) (n : ℕ) :
      Even ((if b then 1 else 0 : ℕ) + 2 * n) ↔ b = false := by
    cases b <;> simp [Nat.even_add]
  have hi (i : Fin d) :
      Even ((if i.castSucc ∈ P then 1 else 0 : ℕ) +
        (if i.succ ∈ P then 1 else 0) + (if a i then 1 else 0)) ↔
      decide (i.succ ∈ P) = Bool.xor (decide (i.castSucc ∈ P)) (a i) := by
    simpa using even_three_bits (decide (i.castSucc ∈ P)) (decide (i.succ ∈ P)) (a i)
  simp_rw [hi]
  have hzero := he (decide ((0 : Fin (d + 1)) ∈ P)) (if false ∈ L then 1 else 0)
  have hlast := he (decide (Fin.last d ∈ P)) (if true ∈ L then 1 else 0)
  simpa only [Bool.decide_coe, decide_eq_true_eq] using and_congr hzero (and_congr hlast Iff.rfl)

def parityEdges {d : ℕ} (a : Fin d → Bool) : Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun j => parityScan false a j)

theorem membership_eq_parityScan_iff {d : ℕ} (a : Fin d → Bool) (P : Finset (Fin (d + 1))) :
    (fun i => decide (i ∈ P)) = parityScan false a ↔ P = parityEdges a := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun b : Bool => b = true) (congrFun h i)
    simpa [parityEdges] using hi
  · rintro rfl
    funext i
    simp [parityEdges]

/-- For every degree, the path is uniquely forced by the input port set;
the two endpoint loops are completely free choices. -/
theorem localEven_iff {d : ℕ} (a : Fin d → Bool)
    (P : Finset (Fin (d + 1))) (L : Finset Bool) :
    LocalEven a P L ↔ Even (∑ i, (if a i then 1 else 0 : ℕ)) ∧ P = parityEdges a := by
  rw [localEven_iff_parityPath, parityPath_iff, membership_eq_parityScan_iff]

theorem forall_fin_endpoints {d : ℕ} (P : Fin (d + 2) → Prop) :
    (∀ j, P j) ↔ P 0 ∧ P (Fin.last (d + 1)) ∧ ∀ i : Fin d, P i.succ.castSucc := by
  constructor
  · intro h
    exact ⟨h _, h _, fun i => h _⟩
  · rintro ⟨h0, hlast, hi⟩ j
    refine Fin.cases h0 (fun k => ?_) j
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simpa only [Fin.succ_last] using hlast
    · simpa only [Fin.succ_castSucc] using hi i

end PlanarHom.Fisher

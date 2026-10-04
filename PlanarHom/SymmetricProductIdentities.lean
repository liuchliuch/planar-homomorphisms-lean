import PlanarHom.FixedLengthProductRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact transport between the paper's upper-triangular product alphabet and
the compiler's ordered q²-entry alphabet. Symmetry, factor count and all zeros
are preserved; the compiler does not assume extra ordered-entry identities. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SymmetricProductIdentities
attribute [local instance 2000] instBEqOfDecidableEq
open Complexity.MixedCode ExponentProductSemantics

abbrev Upper (q : ℕ) := {p : Fin q × Fin q // p.1 ≤ p.2}

def orient {q : ℕ} (p : Fin q × Fin q) : Upper q :=
  if h : p.1 ≤ p.2 then ⟨p, h⟩ else ⟨(p.2, p.1), le_of_not_ge h⟩

theorem entry_orient {K : Type*} {q : ℕ} (M : Matrix (Fin q) (Fin q) K)
    (hM : ∀ i j, M i j = M j i) (p : Fin q × Fin q) :
    M (orient p).val.1 (orient p).val.2 = M p.1 p.2 := by
  unfold orient
  split_ifs
  · rfl
  · exact hM p.2 p.1

private theorem sum_counts {E : Type*} [Fintype E] [DecidableEq E] (w : List E) :
    (∑ e, w.count e) = w.length := by
  induction w with
  | nil => simp
  | cons e w ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
    have h : (∑ i : E, if e == i then 1 else 0) = 1 := by simp
    rw [h, ih]

private theorem product_counts {K E : Type*} [CommMonoid K] [Fintype E] [DecidableEq E]
    (A : E → K) (w : List E) : (w.map A).prod = ∏ e, A e ^ w.count e := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro e _ he
  rw [List.count_eq_zero_of_not_mem (by simpa using he), pow_zero]

def upperWord (q : ℕ) (xs : List ℕ) : List (Upper q) :=
  (expand (q * q) xs).map (fun i => orient (finProdFinEquiv.symm i))

theorem upperWord_count_sum {q m : ℕ} (xs : List ℕ)
    (hx : xs ∈ ExponentVectors.weak (q * q) m) :
    (∑ e : Upper q, (upperWord q xs).count e) = m := by
  have hc := sum_counts (upperWord q xs)
  change (∑ e : Upper q, (upperWord q xs).count e) = (upperWord q xs).length at hc
  rw [hc]
  obtain ⟨hl, hs⟩ := (ExponentVectors.mem_weak _ _ _).mp hx
  simpa only [upperWord, List.length_map, expand_length xs hl] using hs

theorem value_eq_upper_product {K : Type} [Field K] {q : ℕ}
    (M : Matrix (Fin q) (Fin q) K) (hM : ∀ i j, M i j = M j i) (xs : List ℕ) :
    value (binaryAlphabet M) xs =
      ∏ e : Upper q, M e.val.1 e.val.2 ^ (upperWord q xs).count e := by
  have hc := product_counts (fun e : Upper q => M e.val.1 e.val.2) (upperWord q xs)
  change ((upperWord q xs).map (fun e : Upper q => M e.val.1 e.val.2)).prod =
    (∏ e : Upper q, M e.val.1 e.val.2 ^ (upperWord q xs).count e) at hc
  rw [← hc, upperWord, List.map_map, ← expand_product]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  exact (entry_orient M hM (finProdFinEquiv.symm i)).symm

/-- The literal source condition (iv) implies the ordered-codeword identity
condition, without positivity assumptions on the replacement matrix. -/
theorem ordered_identity_of_upper {q m : ℕ}
    (F : ℝ → Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin q) ℝ)
    (hF : ∀ x i j, F x i j = F x j i) (hB : ∀ i j, B i j = B j i)
    (hidentity : ∀ a b : Upper q → ℕ, (∑ e, a e) = m → (∑ e, b e) = m →
      (fun x : ℝ => ∏ e, F x e.val.1 e.val.2 ^ a e) =
        (fun x : ℝ => ∏ e, F x e.val.1 e.val.2 ^ b e) →
      (∏ e, B e.val.1 e.val.2 ^ a e) = ∏ e, B e.val.1 e.val.2 ^ b e) :
    ∀ xs ∈ ExponentVectors.weak (q * q) m, ∀ ys ∈ ExponentVectors.weak (q * q) m,
      (fun x => value (binaryAlphabet (F x)) xs) =
        (fun x => value (binaryAlphabet (F x)) ys) →
      value (binaryAlphabet B) xs = value (binaryAlphabet B) ys := by
  intro xs hxs ys hys he
  rw [value_eq_upper_product B hB, value_eq_upper_product B hB]
  apply hidentity _ _ (upperWord_count_sum xs hxs) (upperWord_count_sum ys hys)
  funext x
  simpa only [value_eq_upper_product (F x) (hF x)] using congrFun he x

end PlanarHom.SymmetricProductIdentities

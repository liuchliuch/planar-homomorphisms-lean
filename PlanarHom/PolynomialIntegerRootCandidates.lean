import PlanarHom.PolynomialDiscretePartition
import PlanarHom.ListMapMachines
import Mathlib.Algebra.Polynomial.Roots

/-! # Constant-size lists containing every bounded integer root

A nonzero degree-`d` polynomial cannot vanish on `d+1` consecutive integers.
Consequently every zero interval in the discrete sign partition has length at
most `d`. Taking the first `d` integers of every sign interval supplies all roots
in the requested interval, with at most `d * 3^d` candidates.
-/

noncomputable section
namespace PlanarHom.PolynomialIntegerRootCandidates
open PolynomialDiscretePartition DiscreteSignPartition

def candidates (d : ℕ) (p : Polynomial ℚ) (l h : ℕ) : List ℕ :=
  (partition d p l h).flatMap (fun I => (List.range d).map (fun j => I.1+j))

theorem zero_interval_short (p : Polynomial ℚ) (d : ℕ) (hp : p.natDegree ≤ d)
    (hne : p ≠ 0) (l t : ℕ) (hzero : ∀ j, l ≤ j → j ≤ t → values p j = 0) :
    t < l+d := by
  by_contra ht
  apply hne
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun i : Fin (d+1) => ((l+i.val : ℕ) : ℚ))
  · intro a b hab
    have he : l+a.val = l+b.val := Nat.cast_injective hab
    apply Fin.ext
    omega
  · intro i
    exact hzero (l+i.val) (by omega) (by omega)
  · simp only [Fintype.card_fin]
    omega

theorem root_mem_candidates (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d)
    (hne : p ≠ 0) (l h t : ℕ) (hl : l ≤ t) (hh : t < h)
    (hroot : p.eval (t : ℚ) = 0) : t ∈ candidates d p l h := by
  obtain ⟨hb, hs, hv⟩ := partition_bounds d p hp l h (by omega)
  obtain ⟨I, hI, hlo, hhi⟩ := hv t hl hh
  have hz : ∀ j, I.1 ≤ j → j < I.2 → values p j = 0 := by
    rcases hs I hI with hn | hz | hp'
    · have hn' := hn t hlo hhi
      change p.eval (t:ℚ) < 0 at hn'
      rw [hroot] at hn'
      exact (lt_irrefl _ hn').elim
    · exact hz
    · have hp'' := hp' t hlo hhi
      change 0 < p.eval (t:ℚ) at hp''
      rw [hroot] at hp''
      exact (lt_irrefl _ hp'').elim
  have ht : t < I.1+d := zero_interval_short p d hp hne I.1 t
    (fun j hj hj' => hz j hj (by omega))
  apply List.mem_flatMap.mpr
  refine ⟨I, hI, ?_⟩
  apply List.mem_map.mpr
  exact ⟨t-I.1, List.mem_range.mpr (by omega), Nat.add_sub_of_le hlo⟩

theorem partition_length (d : ℕ) (p : Polynomial ℚ) (l h : ℕ) :
    (partition d p l h).length ≤ 3^d := by
  induction d generalizing p with
  | zero => simp [partition]
  | succ d ih =>
    rw [partition, List.length_flatMap]
    have hs := ListMapMachines.sum_map_le_mul
      (fun I => (split p I).length) (partition d (difference p) l h) 3
      (fun I _ => splitIncreasing_length _ _ _)
    have hi := ih (difference p)
    rw [pow_succ]
    exact hs.trans (Nat.mul_le_mul_right 3 hi)

theorem candidates_length (d : ℕ) (p : Polynomial ℚ) (l h : ℕ) :
    (candidates d p l h).length ≤ 3^d*d := by
  unfold candidates
  rw [List.length_flatMap]
  have hs := ListMapMachines.sum_map_le_mul
    (fun I => ((List.range d).map (fun j => I.1+j)).length) (partition d p l h) d
    (fun I _ => by simp)
  exact hs.trans (Nat.mul_le_mul_right d (partition_length d p l h))

end PlanarHom.PolynomialIntegerRootCandidates

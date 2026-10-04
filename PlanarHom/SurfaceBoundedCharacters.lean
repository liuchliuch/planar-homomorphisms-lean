import PlanarHom.SurfaceBooleanQuotientMachines

/-! NEW fixed-bound character enumeration. The lookup table is fixed at 2g;
raw inputs of larger computed rank produce the empty list, never exponential
work in an unbounded input rank. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines

def allWords : ℕ → List Row
  | 0 => [[]]
  | n+1 => (allWords n).flatMap (fun r => [false::r,true::r])

def boundedWords (bound d : ℕ) : List Row :=
  ((List.range (bound+1)).map allWords)[d]?.getD []

@[simp] theorem allWords_length (n : ℕ) : (allWords n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [allWords,List.length_flatMap]
      simp [ih,pow_succ,Nat.mul_comm]

theorem mem_allWords (n : ℕ) (r : Row) : r∈allWords n ↔ r.length=n := by
  induction n generalizing r with
  | zero => simp [allWords]
  | succ n ih =>
      cases r with
      | nil => simp [allWords]
      | cons b r =>
          cases b <;> simp [allWords,ih]

theorem allWords_nodup (n : ℕ) : (allWords n).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
      rw [allWords,List.nodup_flatMap]
      constructor
      · intro r hr
        simp
      · apply ih.imp
        intro r s hrs
        apply List.disjoint_left.mpr
        intro t ht hs
        simp at ht hs
        rcases ht with rfl | rfl <;> rcases hs with hs | hs <;> simp_all

theorem boundedWords_eq (bound d : ℕ) :
    boundedWords bound d=if d≤bound then allWords d else [] := by
  by_cases h : d≤bound
  · simp [boundedWords,h,show d<bound+1 by omega]
  · simp [boundedWords,h,show ¬d<bound+1 by omega]

theorem boundedWords_size (bound d : ℕ) : (boundedWords bound d).length≤2^bound := by
  rw [boundedWords_eq]
  split
  · rename_i h
    rw [allWords_length]
    exact Nat.pow_le_pow_right (by omega) h
  · simp

theorem fp_boundedWords (bound : ℕ) : FP BitEncoding.nat rowCode.list (boundedWords bound) :=
  ((fp_const BitEncoding.nat rowCode.list.list ((List.range (bound+1)).map allWords)).pair
    (fp_id BitEncoding.nat)).comp (FisherCodeMachines.fp_getD rowCode.list [])

end PlanarHom.SurfaceBooleanRows

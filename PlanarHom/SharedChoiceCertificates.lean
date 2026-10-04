import PlanarHom.MaterializedCoefficientHeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Shared coordinate denominators across finite choices. Exponential sums of
expanded products retain one denominator; their bit bound pays logarithmically
for the number of terms rather than multiplying denominators term by term. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SharedChoiceCertificates
open FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

/-- All possible values at one factor position receive the same denominator. -/
def common {I : Type} [Fintype I] (f : I→K) (a : ∀i,Certificate basis (f i)) (i : I) :
    Certificate basis (f i) where
  denominator:=∏j,(a j).denominator
  denominator_pos:=Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _=>(a j).denominator_pos.ne'))
  numerator:=fun k=>(a i).numerator k*(∏j∈Finset.univ.erase i,(a j).denominator : ℕ)
  spec:=by
    intro k
    rw [←Finset.prod_erase_mul Finset.univ (fun j=>(a j).denominator) (Finset.mem_univ i)]
    simp only [Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    rw [mul_assoc,(a i).spec]
    ring

theorem common_bounded {I : Type} [Fintype I] (f : I→K) (a : ∀i,Certificate basis (f i))
    (H : ℕ) (hH : 1≤H) (ha : ∀i,(a i).Bounded H H) (i : I) :
    (common f a i).Bounded (H^(Fintype.card I+1)) (H^(Fintype.card I+1)) := by
  have hpos : 0<H:=Nat.zero_lt_of_lt hH
  have hp (s : Finset I) : (∏j∈s,(a j).denominator)≤H^s.card := by
    simpa using Finset.prod_le_prod' (s:=s) (fun j _=>(ha j).1)
  constructor
  · exact (hp Finset.univ).trans (Nat.pow_le_pow_right hpos (by simp))
  · intro k
    change ((a i).numerator k*(∏j∈Finset.univ.erase i,(a j).denominator : ℕ)).natAbs≤_
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    calc
      _≤H*H^(Finset.univ.erase i).card:=Nat.mul_le_mul ((ha i).2 k) (hp _)
      _≤H*H^(Fintype.card I):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (Finset.card_le_univ _))
      _=H^(Fintype.card I+1):=(pow_succ' H _).symm

variable {J I : Type} [Fintype J] [Fintype I]

def term (data : ClearedCoordinates basis (fun k : Fin dimension=>basis k))
    (f : J→I→K) (a : ∀j i,Certificate basis (f j i)) (j : J) :
    Certificate basis (∏i,f j i) :=
  let p:=Certificate.product data (f j) (a j) Finset.univ.toList
  { denominator:=p.denominator
    denominator_pos:=p.denominator_pos
    numerator:=p.numerator
    spec:=by intro k; simpa [p] using p.spec k }

theorem term_denominator (data : ClearedCoordinates basis (fun k : Fin dimension=>basis k))
    (f : J→I→K) (a : ∀j i,Certificate basis (f j i))
    (hden : ∀j j' i,(a j i).denominator=(a j' i).denominator) (j j' : J) :
    (term data f a j).denominator=(term data f a j').denominator := by
  exact MaterializedCoefficientHeights.product_denominator_congr data (f j) (f j') (a j) (a j')
    (hden j j') Finset.univ.toList

def selectedSum (data : ClearedCoordinates basis (fun k : Fin dimension=>basis k))
    (f : J→I→K) (a : ∀j i,Certificate basis (f j i))
    (hden : ∀j j' i,(a j i).denominator=(a j' i).denominator)
    (j₀ : J) (P : J→Prop) : Certificate basis (∑j,if P j then ∏i,f j i else 0) where
  denominator:=(term data f a j₀).denominator
  denominator_pos:=(term data f a j₀).denominator_pos
  numerator:=fun k=>∑j,if P j then (term data f a j).numerator k else 0
  spec:=by
    intro k
    simp only [map_sum,Finset.sum_apply,Finset.mul_sum,Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rw [←term_denominator data f a hden j j₀]
      exact (term data f a j).spec k
    · simp

theorem selectedSum_bounded (data : ClearedCoordinates basis (fun k : Fin dimension=>basis k))
    (f : J→I→K) (a : ∀j i,Certificate basis (f j i))
    (hden : ∀j j' i,(a j i).denominator=(a j' i).denominator)
    (j₀ : J) (P : J→Prop) (H : ℕ) (hH : 1≤H) (ha : ∀j i,(a j i).Bounded H H) :
    (selectedSum data f a hden j₀ P).Bounded
      (Fintype.card J*(Certificate.heightConstant data*H)^(Fintype.card I+1))
      ((Certificate.heightConstant data*H)^(Fintype.card I+1)) := by
  have ht (j : J) : (term data f a j).Bounded
      ((Certificate.heightConstant data*H)^(Fintype.card I+1))
      ((Certificate.heightConstant data*H)^(Fintype.card I+1)) := by
    simpa [term] using Certificate.product_bounded data (f j) (a j) Finset.univ.toList hH (ha j)
  constructor
  · exact (ht j₀).1
  · intro k
    apply (natAbs_sum_le _ _).trans
    calc
      _≤∑_j : J,(Certificate.heightConstant data*H)^(Fintype.card I+1) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact (ht j).2 k
        · simp
      _=_ := by simp

end PlanarHom.SharedChoiceCertificates

import PlanarHom.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# An explicit all-k radial tile

An onion of rings of lengths 4,12,...,8k-4 is modified by endpoint switches
along a specified internal long matching. The definitions are total at k=0.
This module does not claim planarity, the two-state boundary theorem, or the
selected Potts coefficient identity until those properties have been proved.
-/
open scoped BigOperators
namespace PlanarHom.RadialPottsTile

abbrev White (k : ℕ) := (r : Fin k) × Fin (8*r.val+4)
abbrev Port (k : ℕ) := Fin 4 × Fin k
abbrev Vertex (k : ℕ) := White k ⊕ Port k
abbrev Long (k : ℕ) := (r : Fin k) × (Fin 4 × Fin (r.val+1))
abbrev HalfShort (k : ℕ) := (r : Fin k) × Fin (4*r.val+2)
abbrev Edge (k : ℕ) := Long k ⊕ (HalfShort k × Bool)

/-- Simultaneously exchange the ends of the selected internal long matching
(r,0,0)--(r+1,0,1). All transpositions have disjoint supports. -/
def switch {k : ℕ} (w : White k) : White k :=
  if h₀ : w.2.val=0 ∧ w.1.val+1<k then
    ⟨⟨w.1.val+1,h₀.2⟩,⟨1,by omega⟩⟩
  else if h₁ : w.2.val=1 ∧ 0<w.1.val then
    ⟨⟨w.1.val-1,by omega⟩,⟨0,by omega⟩⟩
  else w

def longLeft {k : ℕ} (e : Long k) : White k :=
  ⟨e.1,⟨e.2.1.val*(2*e.1.val+1)+2*e.2.2.val,by
    have hs := e.2.1.isLt
    have ha := e.2.2.isLt
    have hh := Nat.mul_le_mul_right (2*e.1.val+1) (show e.2.1.val≤3 by omega)
    omega⟩⟩

def longRight {k : ℕ} (e : Long k) : Vertex k :=
  if h : e.1.val+1<k then
    .inl ⟨⟨e.1.val+1,h⟩,
      ⟨e.2.1.val*(2*(e.1.val+1)+1)+2*e.2.2.val+1,by
        have hs := e.2.1.isLt
        have ha := e.2.2.isLt
        have hh := Nat.mul_le_mul_right (2*(e.1.val+1)+1)
          (show e.2.1.val≤3 by omega)
        change _ < 8*(e.1.val+1)+4
        omega⟩⟩
  else .inr ⟨e.2.1,⟨e.2.2.val,by have := e.2.2.isLt; have := e.1.isLt; omega⟩⟩

def evenWhite {k : ℕ} (e : HalfShort k) : White k :=
  ⟨e.1,⟨2*e.2.val,by have := e.2.isLt; omega⟩⟩

def oddWhite {k : ℕ} (e : HalfShort k) : White k :=
  ⟨e.1,⟨2*e.2.val+1,by have := e.2.isLt; omega⟩⟩

def nextWhite {k : ℕ} (e : HalfShort k) : White k :=
  ⟨e.1,⟨(2*e.2.val+2)%(8*e.1.val+4),Nat.mod_lt _ (by omega)⟩⟩

/-- Red short edges are switched; blue short edges are unchanged. -/
def graph (k : ℕ) : MultiGraph (Vertex k) (Edge k) where
  src := Sum.elim (fun e => .inl (longLeft e))
    (fun e => .inl (if e.2 then oddWhite e.1 else switch (evenWhite e.1)))
  dst := Sum.elim longRight
    (fun e => .inl (if e.2 then nextWhite e.1 else switch (oddWhite e.1)))

theorem white_ext {k : ℕ} (u v : White k)
    (hr : u.1.val=v.1.val) (hi : u.2.val=v.2.val) : u=v := by
  rcases u with ⟨r,i⟩
  rcases v with ⟨s,j⟩
  have hrs : r=s := Fin.ext hr
  subst s
  have hij : i=j := Fin.ext hi
  subst j
  rfl

theorem switch_involutive {k : ℕ} : Function.Involutive (@switch k) := by
  intro ⟨r,i⟩
  by_cases h₀ : i.val=0 ∧ r.val+1<k
  · have hf : switch (⟨r,i⟩ : White k) =
        ⟨⟨r.val+1,h₀.2⟩,⟨1,by omega⟩⟩ := dif_pos h₀
    rw [hf]
    rw [switch, dif_neg (show ¬((1:ℕ)=0 ∧ r.val+1+1<k) by omega),
      dif_pos (show (1:ℕ)=1 ∧ 0<r.val+1 by omega)]
    apply white_ext <;> dsimp <;> omega
  · by_cases h₁ : i.val=1 ∧ 0<r.val
    · have hf : switch (⟨r,i⟩ : White k) =
          ⟨⟨r.val-1,by have := r.isLt; omega⟩,⟨0,by omega⟩⟩ := by
        rw [switch, dif_neg h₀, dif_pos h₁]
      rw [hf]
      rw [switch, dif_pos (show (0:ℕ)=0 ∧ r.val-1+1<k by have := r.isLt; omega)]
      apply white_ext <;> dsimp
      · omega
      · rw [Nat.mod_eq_of_lt (show 1<8*(r.val-1+1)+4 by omega)]
        omega
    · have hf : switch (⟨r,i⟩ : White k) = ⟨r,i⟩ := by
        rw [switch, dif_neg h₀, dif_neg h₁]
      rw [hf,hf]


theorem card_white (k : ℕ) : Fintype.card (White k)=4*k^2 := by
  simp only [White,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => 8*r+4) k]
  change (∑ r ∈ Finset.range k, (8*r+4)) = 4*k^2
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem card_halfShort (k : ℕ) : Fintype.card (HalfShort k)=2*k^2 := by
  simp only [HalfShort,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => 4*r+2) k]
  change (∑ r ∈ Finset.range k, (4*r+2)) = 2*k^2
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem card_long (k : ℕ) : Fintype.card (Long k)=2*k*(k+1) := by
  simp only [Long,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => 4*(r+1)) k]
  change (∑ r ∈ Finset.range k, (4*(r+1))) = 2*k*(k+1)
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem card_vertex (k : ℕ) : Fintype.card (Vertex k)=4*k^2+4*k := by
  simp only [Vertex,Fintype.card_sum,card_white,Port,Fintype.card_prod,Fintype.card_fin]

theorem card_short (k : ℕ) : Fintype.card (HalfShort k × Bool)=4*k^2 := by
  simp only [Fintype.card_prod,card_halfShort,Fintype.card_bool]
  ring

theorem card_edge (k : ℕ) : Fintype.card (Edge k)=4*k^2+2*k*(k+1) := by
  simp only [Edge,Fintype.card_sum,card_short,card_long]
  omega

end PlanarHom.RadialPottsTile

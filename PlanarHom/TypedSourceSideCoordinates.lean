import PlanarHom.TypedYFamilyTransport

/-! NEW source-orientation semantics and recovered ambient coordinates.
`Crosses`/`Bipartite.domains` reconstruct the exact predicate shapes demanded by
surviving consumers. This module does not assert an orientation oracle compiler.
The ambientSide definition and its domain lemmas are copied from the recovered
TypedSideSourceAccessOriginal module without proof changes. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealRootRestrictions.Bipartite
variable {C R : Type} [Zero R] {bt : ℕ}

def Crosses (M : Fin bt → Matrix C C R) (side : C → Bool) : Prop :=
  ∀ l i j, M l i j ≠ 0 → side i ≠ side j

def domains (side : C → Bool) : Fin 2 → Set C :=
  fun d => {i | side i = decide (d = 1)}

theorem crosses_iff_same_side_zero (M : Fin bt → Matrix C C R) (side : C → Bool) :
    Crosses M side ↔ ∀ l i j, side i = side j → M l i j = 0 := by
  constructor
  · intro h l i j he
    by_contra hn
    exact h l i j hn he
  · intro h l i j hn he
    exact hn (h l i j he)

theorem crosses_pullback {D : Type} (e : D → C)
    (M : Fin bt → Matrix C C R) (side : C → Bool) (h : Crosses M side) :
    Crosses (fun l i j => M l (e i) (e j)) (fun i => side (e i)) :=
  fun l i j hn => h l (e i) (e j) hn

end PlanarHom.FixedRealRootRestrictions.Bipartite
namespace PlanarHom.TypedSideSourceAccess
open TypedBipartiteContext FixedRealRootRestrictions
variable {x y : ℕ}

def ambientSide (x y : ℕ) (c : Fin (x+y)) : Bool := decide (x≤c.val)

theorem mem_left_iff (c : Fin (x+y)) : c∈domains x y 0 ↔ c.val<x := by
  change (∃i:Fin x,Fin.castAdd y i=c) ↔ _
  constructor
  · rintro ⟨i,rfl⟩; exact i.isLt
  · intro h; exact ⟨⟨c.val,h⟩,Fin.ext rfl⟩

theorem mem_right_iff (c : Fin (x+y)) : c∈domains x y 1 ↔ x≤c.val := by
  change (∃i:Fin y,Fin.natAdd x i=c) ↔ _
  constructor
  · rintro ⟨i,rfl⟩; exact Nat.le_add_right _ _
  · intro h
    refine ⟨⟨c.val-x,by omega⟩,?_⟩
    apply Fin.ext
    change x+(c.val-x)=c.val
    omega

theorem domains_eq_bipartite : domains x y=Bipartite.domains (ambientSide x y) := by
  funext d
  apply Set.ext
  intro c
  fin_cases d
  · change c∈domains x y 0 ↔ c∈Bipartite.domains (ambientSide x y) 0
    rw [mem_left_iff]
    simp [Bipartite.domains,ambientSide]
  · change c∈domains x y 1 ↔ c∈Bipartite.domains (ambientSide x y) 1
    rw [mem_right_iff]
    simp [Bipartite.domains,ambientSide]

@[simp] theorem ambientSide_left (i : Fin x) : ambientSide x y (Fin.castAdd y i) = false := by
  simp [ambientSide, Nat.not_le.mpr i.isLt]

@[simp] theorem ambientSide_right (i : Fin y) : ambientSide x y (Fin.natAdd x i) = true := by
  simp [ambientSide]

theorem ambientSide_swap (c : Fin (y+x)) :
    ambientSide x y (swapColors x y c) = !(ambientSide y x c) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) c <;> simp

end PlanarHom.TypedSideSourceAccess

import PlanarHom.RoutingCellAllocation
import Mathlib.Algebra.BigOperators.Fin

/-! Canonical finite-index allocation for disjoint contiguous-size blocks. This
is a proved finite equivalence, not an assumed variable renumbering. -/
noncomputable section
open Classical
namespace PlanarHom.FiniteBlockAllocation

structure Partition (I : Type) [Fintype I] (initial total : ℕ) where
  base : I → ℕ
  size : I → ℕ
  lower : ∀ i,initial≤base i
  upper : ∀ i,base i+size i≤total
  apart : ∀ i j,i≠j → base i+size i≤base j ∨ base j+size j≤base i
  cardinality : total=initial+∑ i,size i

namespace Partition
variable {I : Type} [Fintype I] {initial total : ℕ}

def toIndex (p : Partition I initial total) : (Fin initial ⊕ (i : I) × Fin (p.size i)) → Fin total
  | .inl i => ⟨i.val,by have h := p.cardinality; omega⟩
  | .inr j => ⟨p.base j.1+j.2.val,by have h := p.upper j.1; omega⟩

theorem toIndex_injective (p : Partition I initial total) : Function.Injective p.toIndex := by
  intro a b he
  have hv := congrArg Fin.val he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext hv)
    | inr b =>
      have h := p.lower b.1
      dsimp [toIndex] at hv
      omega
  | inr a =>
    cases b with
    | inl b =>
      have h := p.lower a.1
      dsimp [toIndex] at hv
      omega
    | inr b =>
      have hij : a.1=b.1 := by
        by_contra hne
        have h := p.apart a.1 b.1 hne
        have ha := a.2.isLt
        have hb := b.2.isLt
        dsimp [toIndex] at hv
        rcases h with h | h <;> omega
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      dsimp only at hij
      subst j
      have hab : a=b := by apply Fin.ext; dsimp [toIndex] at hv; omega
      subst b
      rfl

/-- The total size identity plus disjoint address intervals gives a genuine
bijection covering every declared variable, including empty blocks. -/
def equiv (p : Partition I initial total) : (Fin initial ⊕ (i : I) × Fin (p.size i)) ≃ Fin total :=
  Equiv.ofBijective p.toIndex ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨p.toIndex_injective,by simp [Fintype.card_sum,Fintype.card_sigma,p.cardinality]⟩)

@[simp] theorem equiv_apply (p : Partition I initial total) (x : Fin initial ⊕ (i : I) × Fin (p.size i)) :
    p.equiv x=p.toIndex x := rfl

end Partition
end PlanarHom.FiniteBlockAllocation

namespace PlanarHom.PositiveBlockProgram
open FiniteBlockAllocation ParsimoniousNorOneInThree

theorem width_sum (m : ℕ) (ops : List Instruction) : width m ops=m+(ops.map (fun op => op.1.template.fresh)).sum := by
  induction ops generalizing m with
  | nil => simp [width]
  | cons op ops ih => simp [width,ih,Nat.add_assoc]

theorem sum_get {A : Type} (xs : List A) (f : A → ℕ) :
    (∑ i : Fin xs.length,f (xs.get i))=(xs.map f).sum := by
  rw [←List.sum_ofFn]
  have h : List.ofFn (fun i : Fin xs.length => f (xs.get i))=xs.map f := by
    change List.ofFn (f ∘ xs.get)=_
    rw [←List.map_ofFn,List.ofFn_get]
  rw [h]

def cellPartition (m : ℕ) (cs : List Cell) (h : BaseSequence m cs) :
    Partition (Fin cs.length) m (width m (cs.map Cell.instruction)) where
  base i := (cs.get i).base
  size i := (cs.get i).fresh
  lower i := (baseSequence_bounds cs m h _ (List.get_mem _ _)).1
  upper i := (baseSequence_bounds cs m h _ (List.get_mem _ _)).2
  apart i j hij := by
    have hp := List.pairwise_iff_get.mp (baseSequence_ordered cs m h)
    rcases lt_or_gt_of_ne hij with hl | hg
    · exact Or.inl (hp i j hl)
    · exact Or.inr (hp j i hg)
  cardinality := by
    rw [width_sum,sum_get]
    simp only [List.map_map,Function.comp_def]
    rfl

/-- Exact numeric indexing of original and cell-fresh variables. -/
def canvasAllocation (f : NumericFormula) (hf : NumericValid f) :
    (Fin f.1 ⊕ (i : Fin (canvas f).length) × Fin ((canvas f).get i).fresh) ≃
      Fin (PositiveRoutingCompiler.compile f).1 :=
  (cellPartition f.1 (canvas f) (canvas_bases f hf)).equiv.trans
    (finCongr (by rw [canvas_erase]; rfl))

end PlanarHom.PositiveBlockProgram

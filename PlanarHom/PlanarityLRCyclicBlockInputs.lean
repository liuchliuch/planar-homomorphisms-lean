import PlanarHom.PlanarityLRReversedSlots
import Mathlib.Data.List.Nodup

/-! NEW finite local lane-input family. Expand actual row blocks after the parent,
then wrap to the prefix; fan separation determines its entire numeric order. -/
namespace PlanarHom.PlanarityLRRealization

 theorem flatMap_height_sorted {A B : Type*} (row : List A) (block : A → List B)
    (lo hi : A → ℝ) (height : B → ℝ)
    (hrow : row.Pairwise (fun a b => hi a < lo b))
    (hblock : ∀ a, (block a).Pairwise (fun x y => height x < height y))
    (hbounds : ∀ a x, x ∈ block a → lo a≤height x ∧ height x≤hi a) :
    (row.flatMap block).Pairwise (fun x y => height x < height y) := by
  induction row with
  | nil => simp
  | cons a row ih =>
      have hr := List.pairwise_cons.mp hrow
      rw [List.flatMap_cons,List.pairwise_append]
      refine ⟨hblock a,ih hr.2,?_⟩
      intro x hx y hy
      obtain ⟨b,hb,hby⟩ := List.mem_flatMap.mp hy
      exact (hbounds a x hx).2.trans_lt ((hr.1 b hb).trans_le (hbounds b y hby).1)

 theorem expanded_after_parent_spec {A B : Type*} (pre post : List A) (parent : A) (block : A → List B)
    (lo hi : A → ℝ) (height : B → ℝ)
    (hrow : (pre++parent::post).Pairwise (fun a b => hi a < lo b))
    (hblock : ∀ a, (block a).Pairwise (fun x y => height x < height y))
    (hbounds : ∀ a x, x ∈ block a → lo a≤height x ∧ height x≤hi a) :
    ((post.flatMap block)++pre.flatMap block).Pairwise (fun x y => AfterGapOrder (lo parent) (hi parent) (height x) (height y)) ∧
      ∀ x ∈ (post.flatMap block)++pre.flatMap block, height x < lo parent ∨ hi parent < height x := by
  have hs := List.pairwise_append.mp hrow
  have ht := List.pairwise_cons.mp hs.2.1
  have hpost (x : B) (hx : x ∈ post.flatMap block) : hi parent < height x := by
    obtain ⟨a,ha,hax⟩ := List.mem_flatMap.mp hx
    exact (ht.1 a ha).trans_le (hbounds a x hax).1
  have hpre (x : B) (hx : x ∈ pre.flatMap block) : height x < lo parent := by
    obtain ⟨a,ha,hax⟩ := List.mem_flatMap.mp hx
    exact (hbounds a x hax).2.trans_lt (hs.2.2 a ha parent (List.mem_cons_self ..))
  constructor
  · rw [List.pairwise_append]
    refine ⟨?_,?_,?_⟩
    · apply (flatMap_height_sorted post block lo hi height ht.2 hblock hbounds).imp_of_mem
      intro x y hx hy hxy
      exact Or.inl ⟨hpost x hx,hxy⟩
    · apply (flatMap_height_sorted pre block lo hi height hs.1 hblock hbounds).imp_of_mem
      intro x y hx hy hxy
      exact Or.inr (Or.inl ⟨hxy,hpre y hy⟩)
    · intro x hx y hy
      exact Or.inr (Or.inr ⟨hpost x hx,hpre y hy⟩)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hpost x hx)
    · exact Or.inl (hpre x hx)

/-- Literal after-parent cyclic scan, expanded with the supplied finite child
port lists. Payload identities are retained; only the parent block is omitted. -/
def afterParentInputs {A B : Type*} [DecidableEq A] (row : List A) (parent : A) (block : A → List B) : List B :=
  (row.drop (row.idxOf parent+1)).flatMap block ++ (row.take (row.idxOf parent)).flatMap block

 theorem afterParentInputs_spec {A B : Type*} [DecidableEq A] (row : List A) (parent : A) (block : A → List B)
    (lo hi : A → ℝ) (height : B → ℝ) (hp : parent ∈ row)
    (hrow : row.Pairwise (fun a b => hi a < lo b))
    (hblock : ∀ a, (block a).Pairwise (fun x y => height x < height y))
    (hbounds : ∀ a x, x ∈ block a → lo a≤height x ∧ height x≤hi a) :
    (afterParentInputs row parent block).Pairwise (fun x y => AfterGapOrder (lo parent) (hi parent) (height x) (height y)) ∧
      ∀ x ∈ afterParentInputs row parent block, height x < lo parent ∨ hi parent < height x := by
  have hidx : row.idxOf parent < row.length := List.idxOf_lt_length_iff.mpr hp
  have hsplit := List.take_append_drop (row.idxOf parent) row
  rw [List.drop_eq_getElem_cons hidx,List.getElem_idxOf hidx] at hsplit
  exact expanded_after_parent_spec (row.take (row.idxOf parent)) (row.drop (row.idxOf parent+1)) parent block
    lo hi height (hsplit.symm ▸ hrow) hblock hbounds

 theorem afterParentInputs_indexed_order {A B : Type*} [DecidableEq A] (row : List A) (parent : A) (block : A → List B)
    (lo hi : A → ℝ) (height : B → ℝ) (hp : parent ∈ row)
    (hrow : row.Pairwise (fun a b => hi a < lo b))
    (hblock : ∀ a, (block a).Pairwise (fun x y => height x < height y))
    (hbounds : ∀ a x, x ∈ block a → lo a≤height x ∧ height x≤hi a)
    (i j : Fin (afterParentInputs row parent block).length) (hij : i < j) :
    AfterGapOrder (lo parent) (hi parent) (height (afterParentInputs row parent block)[i]) (height (afterParentInputs row parent block)[j]) := by
  exact List.pairwise_iff_getElem.mp (afterParentInputs_spec row parent block lo hi height hp hrow hblock hbounds).1
    i.val j.val i.isLt j.isLt hij

end PlanarHom.PlanarityLRRealization

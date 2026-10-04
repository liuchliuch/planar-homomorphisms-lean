import PlanarHom.MixedParallelCode

/-! Exact weighted mixed-language semantics and selected-label thickening. -/

namespace PlanarHom.Complexity
open scoped BigOperators
noncomputable section
open Classical

theorem prod_repeatSelected {α R : Type} [Monoid R] (test : α→Bool)
    (s : ℕ) (xs : List α) (f : α→R) :
    ((repeatSelected test s xs).map f).prod =
      (xs.map (fun x=>if test x then f x^s else f x)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h:test x <;> simp [repeatSelected_cons,h,ih]

namespace MixedCode

/-- The exact contribution of one ordered binary occurrence. All coordinates
are checked; a valid code always takes the non-default branch. -/
def binaryValue {C R : Type} [One R] (vertices binaryTypes : ℕ)
    (M : Fin binaryTypes→Matrix C C R) (σ : Fin vertices→C) (e : ℕ × (ℕ × ℕ)) : R :=
  if h : e.1<vertices ∧ e.2.1<vertices ∧ e.2.2<binaryTypes then
    M ⟨e.2.2,h.2.2⟩ (σ ⟨e.1,h.1⟩) (σ ⟨e.2.1,h.2.1⟩) else 1

/-- Every unary occurrence contributes its own fixed-language unary factor. -/
def unaryValue {C R : Type} [One R] (vertices unaryTypes : ℕ)
    (U : Fin unaryTypes→C→R) (σ : Fin vertices→C) (e : ℕ × ℕ) : R :=
  if h : e.1<vertices ∧ e.2<unaryTypes then U ⟨e.2,h.2⟩ (σ ⟨e.1,h.1⟩) else 1

/-- Exact finite assignment sum for a valid mixed instance. Binary and unary
occurrences retain order and multiplicity, and the vertex background occurs
once at every vertex, including isolated vertices. -/
def evaluate {C R : Type} [Fintype C] [CommSemiring R] {binaryTypes unaryTypes : ℕ}
    (g : MixedCode) (_valid : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes→Matrix C C R) (U : Fin unaryTypes→C→R) (w : C→R) : R :=
  ∑ σ : Fin g.vertices→C, (∏ v,w (σ v)) *
    (g.edges.map (binaryValue g.vertices binaryTypes M σ)).prod *
    (g.unaries.map (unaryValue g.vertices unaryTypes U σ)).prod

/-- Selected-label thickening acts only on that interaction matrix. All other
binary labels, every unary occurrence, and the fixed vertex background remain
unchanged. The identity includes loops, repeated occurrences, and `s=0`. -/
theorem evaluate_parallelLabel {C R : Type} [Fintype C] [CommSemiring R]
    {binaryTypes unaryTypes : ℕ} (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected s : ℕ) (M : Fin binaryTypes→Matrix C C R) (U : Fin unaryTypes→C→R) (w : C→R) :
    (g.parallelLabel selected s).evaluate (parallelLabel_valid selected s binaryTypes unaryTypes g hg) M U w =
      g.evaluate hg (fun l i j=>if l.val=selected then M l i j^s else M l i j) U w := by
  unfold evaluate parallelLabel
  apply Finset.sum_congr rfl
  intro σ _
  rw [prod_repeatSelected]
  congr 2
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have hv := hg.1 e he
  by_cases hl : e.2.2=selected <;> simp [binaryValue,hv,hl]

end MixedCode
end
end PlanarHom.Complexity

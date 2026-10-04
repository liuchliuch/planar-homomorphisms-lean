import PlanarHom.MixedParallelSemantics
import PlanarHom.LagrangeRecovery
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Selected-occurrence product semantics for joint interpolation

Every unselected occurrence, unary factor and background vertex weight remains
inside the exact signed assignment coefficient. Lists preserve loops and repeated
occurrences. No planarity or computational reduction is asserted by these identities.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode

variable {C R : Type} [Fintype C] [CommSemiring R] {binaryTypes unaryTypes : ℕ}

/-- Product of all occurrences of one selected binary label in an assignment. -/
def selectedBinaryProduct (g : MixedCode) (selected : ℕ)
    (M : Fin binaryTypes → Matrix C C R) (σ : Fin g.vertices → C) : R :=
  ((g.edges.filter (fun e => e.2.2 = selected)).map (binaryValue g.vertices binaryTypes M σ)).prod

/-- All unchanged contributions, including every vertex and unary occurrence. -/
def binaryRemainder (g : MixedCode) (selected : ℕ)
    (M : Fin binaryTypes → Matrix C C R) (U : Fin unaryTypes → C → R) (w : C → R)
    (σ : Fin g.vertices → C) : R :=
  (∏ v, w (σ v)) *
    ((g.edges.filter (fun e => e.2.2 ≠ selected)).map (binaryValue g.vertices binaryTypes M σ)).prod *
    (g.unaries.map (unaryValue g.vertices unaryTypes U σ)).prod

/-- Exact selected-product splitting, with arbitrary signs permitted in rings. -/
theorem evaluate_eq_binary_product_sum (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : ℕ) (M : Fin binaryTypes → Matrix C C R)
    (U : Fin unaryTypes → C → R) (w : C → R) :
    g.evaluate hg M U w = ∑ σ, binaryRemainder g selected M U w σ * selectedBinaryProduct g selected M σ := by
  unfold evaluate binaryRemainder selectedBinaryProduct
  apply Finset.sum_congr rfl
  intro σ _
  rw [← List.prod_map_filter_mul_prod_map_filter_not (fun e : ℕ × (ℕ × ℕ) => e.2.2 = selected)]
  ring

/-- Unselected binary labels are unchanged in the signed assignment coefficient. -/
theorem binaryRemainder_congr (g : MixedCode) (selected : ℕ)
    (M M' : Fin binaryTypes → Matrix C C R) (U : Fin unaryTypes → C → R) (w : C → R)
    (hM : ∀ l, l.val ≠ selected → M' l = M l) (σ : Fin g.vertices → C) :
    binaryRemainder g selected M' U w σ = binaryRemainder g selected M U w σ := by
  unfold binaryRemainder
  congr 2
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have hsel := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at hsel
  unfold binaryValue
  split
  · rename_i hv
    rw [hM ⟨e.2.2, hv.2.2⟩ hsel]
  · rfl

/-- Powering only the selected matrix powers the entire selected occurrence product. -/
theorem selectedBinaryProduct_power (g : MixedCode) (selected s : ℕ)
    (M : Fin binaryTypes → Matrix C C R) (σ : Fin g.vertices → C) :
    selectedBinaryProduct g selected (fun l i j => if l.val = selected then M l i j ^ s else M l i j) σ =
      selectedBinaryProduct g selected M σ ^ s := by
  unfold selectedBinaryProduct
  have hf : ((g.edges.filter (fun e => e.2.2 = selected)).map
      (binaryValue g.vertices binaryTypes
        (fun l i j => if l.val = selected then M l i j ^ s else M l i j) σ)) =
      (g.edges.filter (fun e => e.2.2 = selected)).map
        (fun e => binaryValue g.vertices binaryTypes M σ e ^ s) := by
    apply List.map_congr_left
    intro e he
    have hsel := (List.mem_filter.mp he).2
    simp only [decide_eq_true_eq] at hsel
    unfold binaryValue
    split <;> simp_all
  rw [hf]
  simpa only [List.map_map, Function.comp_apply] using
    (map_list_prod (powMonoidHom s) ((g.edges.filter (fun e => e.2.2 = selected)).map
      (binaryValue g.vertices binaryTypes M σ))).symm

/-- Every actual parallel query is the finite selected-product power sum. -/
theorem evaluate_parallelLabel_eq_power_sum (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected s : ℕ) (M : Fin binaryTypes → Matrix C C R)
    (U : Fin unaryTypes → C → R) (w : C → R) :
    (g.parallelLabel selected s).evaluate (parallelLabel_valid selected s binaryTypes unaryTypes g hg) M U w =
      ∑ σ, binaryRemainder g selected M U w σ * selectedBinaryProduct g selected M σ ^ s := by
  rw [evaluate_parallelLabel g hg selected s M U w, evaluate_eq_binary_product_sum _ hg selected]
  apply Finset.sum_congr rfl
  intro σ _
  rw [selectedBinaryProduct_power]
  rw [binaryRemainder_congr g selected M _ U w (fun l hl => by ext i j; simp [hl])]

/-- Selected unary occurrences retain their multiplicity independently of the binary language. -/
def selectedUnaryProduct (g : MixedCode) (selected : ℕ)
    (U : Fin unaryTypes → C → R) (σ : Fin g.vertices → C) : R :=
  ((g.unaries.filter (fun e => e.2 = selected)).map (unaryValue g.vertices unaryTypes U σ)).prod

/-- Unchanged binary, background and unselected unary factors. -/
def unaryRemainder (g : MixedCode) (selected : ℕ)
    (M : Fin binaryTypes → Matrix C C R) (U : Fin unaryTypes → C → R) (w : C → R)
    (σ : Fin g.vertices → C) : R :=
  (∏ v, w (σ v)) * (g.edges.map (binaryValue g.vertices binaryTypes M σ)).prod *
    ((g.unaries.filter (fun e => e.2 ≠ selected)).map (unaryValue g.vertices unaryTypes U σ)).prod

theorem evaluate_eq_unary_product_sum (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : ℕ) (M : Fin binaryTypes → Matrix C C R)
    (U : Fin unaryTypes → C → R) (w : C → R) :
    g.evaluate hg M U w = ∑ σ, unaryRemainder g selected M U w σ * selectedUnaryProduct g selected U σ := by
  unfold evaluate unaryRemainder selectedUnaryProduct
  apply Finset.sum_congr rfl
  intro σ _
  rw [← List.prod_map_filter_mul_prod_map_filter_not (fun e : ℕ × ℕ => e.2 = selected)]
  ring

/-- Actual unary replication changes no vertex or binary occurrence. -/
def parallelUnaryLabel (selected s : ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices, g.edges, repeatSelected (fun e => decide (e.2 = selected)) s g.unaries⟩

theorem parallelUnaryLabel_valid (selected s : ℕ) (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) : (g.parallelUnaryLabel selected s).Valid binaryTypes unaryTypes := by
  exact ⟨hg.1, fun u hu => hg.2 u (repeatSelected_mem _ _ _ hu)⟩

theorem evaluate_parallelUnaryLabel (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected s : ℕ) (M : Fin binaryTypes → Matrix C C R)
    (U : Fin unaryTypes → C → R) (w : C → R) :
    (g.parallelUnaryLabel selected s).evaluate (parallelUnaryLabel_valid selected s g hg) M U w =
      g.evaluate hg M (fun l i => if l.val = selected then U l i ^ s else U l i) w := by
  unfold evaluate parallelUnaryLabel
  apply Finset.sum_congr rfl
  intro σ _
  rw [prod_repeatSelected]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have hv := hg.2 e he
  by_cases hl : e.2 = selected <;> simp [unaryValue, hv, hl]

/-- Unselected unary contributions are unaffected by replacing the selected type. -/
theorem unaryRemainder_congr (g : MixedCode) (selected : ℕ)
    (M : Fin binaryTypes → Matrix C C R) (U U' : Fin unaryTypes → C → R) (w : C → R)
    (hU : ∀ l, l.val ≠ selected → U' l = U l) (σ : Fin g.vertices → C) :
    unaryRemainder g selected M U' w σ = unaryRemainder g selected M U w σ := by
  unfold unaryRemainder
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have hsel := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at hsel
  unfold unaryValue
  split
  · rename_i hv
    rw [hU ⟨e.2, hv.2⟩ hsel]
  · rfl

theorem selectedUnaryProduct_power (g : MixedCode) (selected s : ℕ)
    (U : Fin unaryTypes → C → R) (σ : Fin g.vertices → C) :
    selectedUnaryProduct g selected (fun l i => if l.val = selected then U l i ^ s else U l i) σ =
      selectedUnaryProduct g selected U σ ^ s := by
  unfold selectedUnaryProduct
  have hf : ((g.unaries.filter (fun e => e.2 = selected)).map
      (unaryValue g.vertices unaryTypes (fun l i => if l.val = selected then U l i ^ s else U l i) σ)) =
      (g.unaries.filter (fun e => e.2 = selected)).map
        (fun e => unaryValue g.vertices unaryTypes U σ e ^ s) := by
    apply List.map_congr_left
    intro e he
    have hsel := (List.mem_filter.mp he).2
    simp only [decide_eq_true_eq] at hsel
    unfold unaryValue
    split <;> simp_all
  rw [hf]
  simpa only [List.map_map, Function.comp_apply] using
    (map_list_prod (powMonoidHom s) ((g.unaries.filter (fun e => e.2 = selected)).map
      (unaryValue g.vertices unaryTypes U σ))).symm

/-- Actual unary query values obey the same shifted product-sum formula. -/
theorem evaluate_parallelUnaryLabel_eq_power_sum (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected s : ℕ) (M : Fin binaryTypes → Matrix C C R)
    (U : Fin unaryTypes → C → R) (w : C → R) :
    (g.parallelUnaryLabel selected s).evaluate (parallelUnaryLabel_valid selected s g hg) M U w =
      ∑ σ, unaryRemainder g selected M U w σ * selectedUnaryProduct g selected U σ ^ s := by
  rw [evaluate_parallelUnaryLabel g hg selected s M U w, evaluate_eq_unary_product_sum _ hg selected]
  apply Finset.sum_congr rfl
  intro σ _
  rw [selectedUnaryProduct_power]
  rw [unaryRemainder_congr g selected M U _ w (fun l hl => by ext i; simp [hl])]

end PlanarHom.Complexity.MixedCode
